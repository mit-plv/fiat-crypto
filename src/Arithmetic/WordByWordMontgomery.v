Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LinearSubstitute.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module WordByWordMontgomery.
  Section with_args.
    Context (lgr : Z)
            (m : Z).
    Local Notation weight := (uweight lgr).
    Let T (n : nat) := list Z.
    Let r := (2^lgr).
    Definition eval {n} : T n -> Z := Positional.eval weight n.
    Let zero {n} : T n := Positional.zeros n.
    Let divmod {n} : T (S n) -> T n * Z := Rows.divmod.
    Let scmul {n} (c : Z) (p : T n) : T (S n) (* uses double-output multiply *)
      := let '(v, c) := Rows.mul weight r n (S n) (Positional.extend_to_length 1 n [c]) p in
         v.
    Let addT {n} (p q : T n) : T (S n) (* joins carry *)
      := let '(v, c) := Rows.add weight n p q in
         v ++ [c].
    Let drop_high_addT' {n} (p : T (S n)) (q : T n) : T (S n) (* drops carry *)
      := fst (Rows.add weight (S n) p (Positional.extend_to_length n (S n) q)).
    Let conditional_sub {n} (arg : T (S n)) (N : T n) : T n  (* computes [arg - N] if [N <= arg], and drops high bit *)
      := Positional.drop_high_to_length n (Rows.conditional_sub weight (S n) arg (Positional.extend_to_length n (S n) N)).
    Context (R_numlimbs : nat)
            (N : T R_numlimbs). (* encoding of m *)
    Let sub_then_maybe_add (a b : T R_numlimbs) : T R_numlimbs (* computes [a - b + if (a - b) <? 0 then N else 0] *)
      := fst (Rows.sub_then_maybe_add weight R_numlimbs (r-1) a b N).
    Local Opaque T.
    Section Iteration.
      Context (pred_A_numlimbs : nat)
              (B : T R_numlimbs) (k : Z)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs)).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)
      Local Definition A_a := dlet p := @divmod _ A in p. Local Definition A' := fst A_a. Local Definition a := snd A_a.
      Local Definition S1 := @addT _ S (@scmul _ a B).
      Local Definition s := snd (@divmod _ S1).
      Local Definition q := fst (Z.mul_split r s k).
      Local Definition S2 := @drop_high_addT' _ S1 (@scmul _ q N).
      Local Definition S3' := fst (@divmod _ S2).

      Local Definition A'_S3
        := dlet A_a := @divmod _ A in
           dlet A' := fst A_a in
           dlet a := snd A_a in
           dlet S1 := @addT _ S (@scmul _ a B) in
           dlet s := snd (@divmod _ S1) in
           dlet q := fst (Z.mul_split r s k) in
           dlet S2 := @drop_high_addT' _ S1 (@scmul _ q N) in
           dlet S3 := fst (@divmod _ S2) in
           (A', S3).

      Lemma A'_S3_alt : A'_S3 = (A', S3').
      Proof using Type. cbv [A'_S3 A' S3' Let_In S2 q s S1 A' a A_a]; reflexivity. Qed.
    End Iteration.

    Section loop.
      Context (A_numlimbs : nat)
              (A : T A_numlimbs)
              (B : T R_numlimbs)
              (k : Z)
              (S' : T (S R_numlimbs)).

      Definition redc_body {pred_A_numlimbs} : T (S pred_A_numlimbs) * T (S R_numlimbs)
                                               -> T pred_A_numlimbs * T (S R_numlimbs)
        := fun '(A, S') => A'_S3 _ B k A S'.

      Definition redc_loop (count : nat) : T count * T (S R_numlimbs) -> T O * T (S R_numlimbs)
        := nat_rect
             (fun count => T count * _ -> _)
             (fun A_S => A_S)
             (fun count' redc_loop_count' A_S
              => redc_loop_count' (redc_body A_S))
             count.

      Definition pre_redc : T (S R_numlimbs)
        := snd (redc_loop A_numlimbs (A, @zero (1 + R_numlimbs)%nat)).

      Definition redc : T R_numlimbs
        := conditional_sub pre_redc N.
    End loop.

    Create HintDb word_by_word_montgomery.
    Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.

    Definition add (A B : T R_numlimbs) : T R_numlimbs
      := conditional_sub (@addT _ A B) N.
    Definition sub (A B : T R_numlimbs) : T R_numlimbs
      := sub_then_maybe_add A B.
    Definition opp (A : T R_numlimbs) : T R_numlimbs
      := sub (@zero _) A.
    Definition nonzero (A : list Z) : Z
      := fold_right Z.lor 0 A.

    Context (lgr_big : 0 < lgr)
            (R_numlimbs_nz : R_numlimbs <> 0%nat).
    Let R := (r^Z.of_nat R_numlimbs).
    Transparent T.
    Definition small {n} (v : T n) : Prop
      := v = Partition.partition weight n (eval v).
    Context (small_N : small N)
            (N_lt_R : eval N < R)
            (N_nz : 0 < eval N)
            (B : T R_numlimbs)
            (B_bounds : 0 <= eval B < R)
            (small_B : small B)
            ri (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
            (k : Z) (k_correct : k * eval N mod r = (-1) mod r).

    Local Lemma r_big : r > 1.
    Proof using lgr_big. clear -lgr_big; subst r. auto with zarith. Qed.
    Local Notation wprops := (@uwprops lgr lgr_big).

    Local Hint Immediate (wprops) : core.
    Local Hint Immediate (weight_0 wprops) : core.
    Local Hint Immediate (weight_positive wprops) : core.
    Local Hint Immediate (weight_multiples wprops) : core.
    Local Hint Immediate (weight_divides wprops) : core.
    Local Hint Immediate r_big : core.

    Lemma length_small {n v} : @small n v -> length v = n.
    Proof using Type. clear; cbv [small]; intro H; rewrite H; autorewrite with distr_length; reflexivity. Qed.
    Lemma small_bound {n v} : @small n v -> 0 <= eval v < weight n.
    Proof using lgr_big. clear - lgr_big; cbv [small eval]; intro H; rewrite H; autorewrite with push_eval; auto with zarith. Qed.

    Lemma R_plusR_le : R + R <= weight (S R_numlimbs).
    Proof using lgr_big.
      clear - lgr_big.
      etransitivity; [ | apply uweight_double_le; lia ].
      rewrite uweight_eq_alt by lia.
      subst r R; lia.
    Qed.

    Lemma mask_r_sub1 n x :
      map (Z.land (r - 1)) (Partition.partition weight n x) = Partition.partition weight n x.
    Proof using lgr_big.
      clear - lgr_big. cbv [Partition.partition].
      rewrite map_map. apply map_ext; intros.
      rewrite uweight_S by lia.
      rewrite <-Z.mod_pull_div by auto with zarith.
      replace (r - 1) with (Z.ones lgr) by (rewrite Z.ones_equiv; subst r; reflexivity).
      rewrite <-Z.land_comm, Z.land_ones by lia.
      auto with zarith.
    Qed.

    Let partition_Proper := (@Partition.partition_Proper _ wprops).
    Local Existing Instance partition_Proper.
    Lemma eval_nonzero n A : @small n A -> nonzero A = 0 <-> @eval n A = 0.
    Proof using lgr_big.
      clear -lgr_big partition_Proper.
      cbv [nonzero eval small]; intro Heq.
      do 2 rewrite Heq.
      rewrite !eval_partition, Z.mod_mod by auto with zarith.
      generalize (Positional.eval weight n A); clear Heq A.
      induction n as [|n IHn].
      { cbn; rewrite weight_0 by auto; intros; autorewrite with zsimplify_const; lia. }
      { intro; rewrite partition_step.
        rewrite fold_right_snoc, Z.lor_comm, <- fold_right_push, Z.lor_eq_0_iff by auto using Z.lor_assoc.
        assert (Heq : Z.equiv_modulo (weight n) (z mod weight (S n)) (z mod (weight n))).
        { cbv [Z.equiv_modulo].
          generalize (weight_multiples ltac:(auto) n).
          generalize (weight_positive ltac:(auto) n).
          generalize (weight_positive ltac:(auto) (S n)).
          generalize (weight (S n)) (weight n); clear; intros wsn wn.
          clear; intros.
          Z.div_mod_to_quot_rem; subst.
          autorewrite with zsimplify_const in *.
          Z.linear_substitute_all.
          apply Zminus_eq; ring_simplify.
          rewrite <- !Z.add_opp_r, !Z.mul_opp_comm, <- !Z.mul_opp_r, <- !Z.mul_assoc.
          rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
          nia. }
        rewrite Heq at 1; rewrite IHn.
        rewrite Z.mod_mod by auto with zarith.
        generalize (weight_multiples ltac:(auto) n).
        generalize (weight_positive ltac:(auto) n).
        generalize (weight_positive ltac:(auto) (S n)).
        generalize (weight (S n)) (weight n); clear; intros wsn wn; intros.
        Z.div_mod_to_quot_rem.
        repeat (intro || apply conj); destruct_head'_or; try lia; destruct_head'_and; subst; autorewrite with zsimplify_const in *; try nia;
          Z.linear_substitute_all.
        all: apply Zminus_eq; ring_simplify.
        all: rewrite <- ?Z.add_opp_r, ?Z.mul_opp_comm, <- ?Z.mul_opp_r, <- ?Z.mul_assoc.
        all: rewrite <- !Z.mul_add_distr_l, Z.mul_eq_0.
        all: nia. }
    Qed.

    Local Ltac push_step :=
      first [ progress eta_expand
            | rewrite Rows.mul_partitions
            | rewrite Rows.mul_div
            | rewrite Rows.add_partitions
            | rewrite Rows.add_div
            | progress autorewrite with push_eval distr_length
            | match goal with
              | [ H : ?v = _ |- context[length ?v] ] => erewrite length_small by eassumption
              | [ H : small ?v |- context[length ?v] ] => erewrite length_small by eassumption
              end
            | rewrite Positional.eval_cons by distr_length
            | progress rewrite ?weight_0, ?uweight_1 by auto;
              autorewrite with zsimplify_fast
            | rewrite (weight_0 wprops)
            | rewrite <- Z.div_mod'' by auto with lia
            | solve [ trivial ] ].
    Local Ltac push := repeat push_step.

    Local Ltac t_step :=
      match goal with
      | [ H := _ |- _ ] => progress cbv [H] in *
      | _ => progress push_step
      | _ => progress autorewrite with zsimplify_const
      | _ => solve [ auto with lia ]
      end.

    Local Hint Unfold eval zero small divmod scmul drop_high_addT' addT R : loc.
    Local Lemma eval_zero : forall n, eval (@zero n) = 0.
    Proof using Type.
      clear; autounfold with loc; intros; autorewrite with push_eval; auto.
    Qed.
    Local Lemma small_zero : forall n, small (@zero n).
    Proof using Type.
      etransitivity; [ eapply Positional.zeros_ext_map | rewrite eval_zero ]; cbv [Partition.partition]; cbn; try reflexivity; autorewrite with distr_length; reflexivity.
    Qed.
    Local Hint Immediate small_zero : core.

    Ltac push_recursive_partition :=
      repeat match goal with
             | _ => progress cbn [recursive_partition]
             | H : small _ |- _ => rewrite H; clear H
             | _ => rewrite recursive_partition_equiv by auto using wprops
             | _ => rewrite uweight_eval_shift by distr_length
             | _ => progress push
             end.

    Lemma eval_div : forall n v, small v -> eval (fst (@divmod n v)) = eval v / r.
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod fst tl].
      autorewrite with zsimplify; reflexivity.
    Qed.
    Lemma eval_mod : forall n v, small v -> snd (@divmod n v) = eval v mod r.
    Proof using lgr_big.
      clear - lgr_big; intros; autounfold with loc.
      push_recursive_partition; cbn [Rows.divmod snd hd].
      autorewrite with zsimplify; reflexivity.
    Qed.
    Lemma small_div : forall n v, small v -> small (fst (@divmod n v)).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - r_big lgr_big. intros; autounfold with loc.
      push_recursive_partition. cbn [Rows.divmod fst tl].
      rewrite <-recursive_partition_equiv by auto.
      rewrite <-uweight_recursive_partition_equiv with (i:=1%nat) by lia.
      push.
      apply Partition.partition_Proper; [ solve [auto] | ].
      cbv [Z.equiv_modulo]. autorewrite with zsimplify.
      reflexivity.
    Qed.

    Definition canon_rep {n} x (v : T n) : Prop :=
      (v = Partition.partition weight n x) /\ (0 <= x < weight n).
    Lemma eval_canon_rep n x v : @canon_rep n x v -> eval v = x.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      auto using Z.mod_small.
    Qed.
    Lemma small_canon_rep n x v : @canon_rep n x v -> small v.
    Proof using lgr_big.
      clear - lgr_big.
      cbv [canon_rep eval small]; intros [Hv Hx].
      rewrite Hv. autorewrite with push_eval.
      apply partition_eq_mod; auto; [ ].
      Z.rewrite_mod_small; reflexivity.
    Qed.

    Local Lemma scmul_correct: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> canon_rep (a * eval v) (@scmul n a v).
    Proof using lgr_big.
      pose proof r_big as r_big.
      clear - lgr_big r_big.
      autounfold with loc; intro n; destruct (zerop n); intros *; intro Hsmall; intros.
      { intros; subst; cbn; rewrite Z.add_with_get_carry_full_mod.
        split; cbn; autorewrite with zsimplify_fast; auto with zarith. }
      { rewrite (surjective_pairing (Rows.mul _ _ _ _ _ _)).
        rewrite Rows.mul_partitions by (try rewrite Hsmall; auto using length_partition, Positional.length_extend_to_length with lia).
        autorewrite with push_eval zsimplify_fast.
        split; [reflexivity | ].
        rewrite uweight_S, uweight_eq_alt by lia.
        subst r; nia. }
    Qed.

    Local Lemma addT_correct : forall n a b, small a -> small b -> canon_rep (eval a + eval b) (@addT n a b).
    Proof using lgr_big.
      intros n a b Ha Hb.
      generalize (length_small Ha); generalize (length_small Hb).
      generalize (small_bound Ha); generalize (small_bound Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc; destruct (zerop n); subst.
      { destruct a, b; cbn; try lia; split; auto with zarith. }
      { pose proof (uweight_double_le lgr ltac:(lia) n).
        eta_expand; split; [ | lia ].
        rewrite Rows.add_partitions, Rows.add_div by auto.
        rewrite partition_step.
        Z.rewrite_mod_small; reflexivity. }
    Qed.

    Local Lemma drop_high_addT'_correct : forall n a b, small a -> small b -> canon_rep ((eval a + eval b) mod (r^Z.of_nat (S n))) (@drop_high_addT' n a b).
    Proof using lgr_big.
      intros n a b Ha Hb; generalize (length_small Ha); generalize (length_small Hb).
      clear -lgr_big Ha Hb.
      autounfold with loc in *; subst; intros.
      rewrite Rows.add_partitions by auto using Positional.length_extend_to_length.
      autorewrite with push_eval.
      split; try apply partition_eq_mod; auto; rewrite uweight_eq_alt by lia; subst r; Z.rewrite_mod_small; auto with zarith.
    Qed.

    Local Lemma conditional_sub_correct : forall v, small v -> 0 <= eval v < eval N + R -> canon_rep (eval v + (if eval N <=? eval v then -eval N else 0)) (conditional_sub v N).
    Proof using small_N lgr_big N_nz N_lt_R.
      pose proof R_plusR_le as R_plusR_le.
      clear - small_N lgr_big N_nz N_lt_R R_plusR_le.
      intros; autounfold with loc; cbv [conditional_sub].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      autorewrite with push_eval.
      assert (weight R_numlimbs < weight (S R_numlimbs)) by (rewrite !uweight_eq_alt by lia; autorewrite with push_Zof_nat; auto with zarith).
      assert (eval N mod weight R_numlimbs < weight (S R_numlimbs)) by (pose proof (Z.mod_pos_bound (eval N) (weight R_numlimbs) ltac:(auto)); lia).
      rewrite Rows.conditional_sub_partitions by (repeat (autorewrite with distr_length push_eval; auto using partition_eq_mod with zarith)).
      rewrite drop_high_to_length_partition by lia.
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst R; reflexivity).
      Z.rewrite_mod_small.
      break_match; autorewrite with zsimplify_fast; Z.ltb_to_lt.
      { split; [ reflexivity | ].
        rewrite Z.add_opp_r. fold (eval N).
        auto using Z.mod_small with lia. }
      { split; auto using Z.mod_small with lia. }
    Qed.

    Local Lemma sub_then_maybe_add_correct : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> canon_rep (eval a - eval b + (if eval a - eval b <? 0 then eval N else 0)) (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
      pose proof mask_r_sub1 as mask_r_sub1.
      clear - small_N lgr_big R_numlimbs_nz N_nz N_lt_R mask_r_sub1.
      intros; autounfold with loc; cbv [sub_then_maybe_add].
      repeat match goal with H : small _ |- _ =>
                             rewrite H; clear H end.
      rewrite Rows.sub_then_maybe_add_partitions by (autorewrite with push_eval distr_length; auto with zarith).
      autorewrite with push_eval.
      assert (weight R_numlimbs = R) by (rewrite uweight_eq_alt by lia; subst r R; reflexivity).
      Z.rewrite_mod_small.
      split; [ reflexivity | ].
      break_match; Z.ltb_to_lt; lia.
    Qed.

    Local Lemma eval_scmul: forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> eval (@scmul n a v) = a * eval v.
    Proof using lgr_big. eauto using scmul_correct, eval_canon_rep. Qed.
    Local Lemma small_scmul : forall n a v, small v -> 0 <= a < r -> 0 <= eval v < r^Z.of_nat n -> small (@scmul n a v).
    Proof using lgr_big. eauto using scmul_correct, small_canon_rep. Qed.
    Local Lemma eval_addT : forall n a b, small a -> small b -> eval (@addT n a b) = eval a + eval b.
    Proof using lgr_big. eauto using addT_correct, eval_canon_rep. Qed.
    Local Lemma small_addT : forall n a b, small a -> small b -> small (@addT n a b).
    Proof using lgr_big. eauto using addT_correct, small_canon_rep. Qed.
    Local Lemma eval_drop_high_addT' : forall n a b, small a -> small b -> eval (@drop_high_addT' n a b) = (eval a + eval b) mod (r^Z.of_nat (S n)).
    Proof using lgr_big. eauto using drop_high_addT'_correct, eval_canon_rep. Qed.
    Local Lemma small_drop_high_addT' : forall n a b, small a -> small b -> small (@drop_high_addT' n a b).
    Proof using lgr_big. eauto using drop_high_addT'_correct, small_canon_rep. Qed.
    Local Lemma eval_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v N) = eval v + (if eval N <=? eval v then -eval N else 0).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, eval_canon_rep. Qed.
    Local Lemma small_conditional_sub : forall v, small v -> 0 <= eval v < eval N + R -> small (conditional_sub v N).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using conditional_sub_correct, small_canon_rep. Qed.
    Local Lemma eval_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> eval (sub_then_maybe_add a b) = eval a - eval b + (if eval a - eval b <? 0 then eval N else 0).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, eval_canon_rep. Qed.
    Local Lemma small_sub_then_maybe_add : forall a b, small a -> small b -> 0 <= eval a < eval N -> 0 <= eval b < eval N -> small (sub_then_maybe_add a b).
    Proof using small_N lgr_big R_numlimbs_nz N_nz N_lt_R. eauto using sub_then_maybe_add_correct, small_canon_rep. Qed.

    Local Opaque T addT drop_high_addT' divmod zero scmul conditional_sub sub_then_maybe_add.
    Create HintDb push_mont_eval discriminated.
    Create HintDb word_by_word_montgomery.
    Hint Unfold A'_S3 S3' S2 q s S1 a A' A_a Let_In : word_by_word_montgomery.
    Let r_big' := r_big. (* to put it in the context *)
    Local Ltac t_small :=
      repeat first [ assumption
                   | apply small_addT
                   | apply small_drop_high_addT'
                   | apply small_div
                   | apply small_zero
                   | apply small_scmul
                   | apply small_conditional_sub
                   | apply small_sub_then_maybe_add
                   | apply Z_mod_lt
                   | rewrite Z.mul_split_mod
                   | solve [ auto with zarith ]
                   | lia
                   | progress autorewrite with push_mont_eval
                   | progress autounfold with word_by_word_montgomery
                   | match goal with
                     | [ H : and _ _ |- _ ] => destruct H
                     end ].
    Hint Rewrite
         eval_zero
         eval_div
         eval_mod
         eval_addT
         eval_drop_high_addT'
         eval_scmul
         eval_conditional_sub
         eval_sub_then_maybe_add
         using (repeat autounfold with word_by_word_montgomery; t_small)
      : push_mont_eval.

    Local Arguments eval {_} _.
    Local Arguments small {_} _.
    Local Arguments divmod {_} _.

    (* Recurse for a as many iterations as A has limbs, varying A := A, S := 0, r, bounds *)
    Section Iteration_proofs.
      Context (pred_A_numlimbs : nat)
              (A : T (S pred_A_numlimbs))
              (S : T (S R_numlimbs))
              (small_A : small A)
              (small_S : small S)
              (S_nonneg : 0 <= eval S).
      (* Given A, B < R, we want to compute A * B / R mod N. R = bound 0 * ... * bound (n-1) *)

      Local Coercion eval : T >-> Z.

      Local Notation a := (@a pred_A_numlimbs A).
      Local Notation A' := (@A' pred_A_numlimbs A).
      Local Notation S1 := (@S1 pred_A_numlimbs B A S).
      Local Notation s := (@s pred_A_numlimbs B A S).
      Local Notation q := (@q pred_A_numlimbs B k A S).
      Local Notation S2 := (@S2 pred_A_numlimbs B k A S).
      Local Notation S3 := (@S3' pred_A_numlimbs B k A S).

      Local Notation eval_pre_S3 := ((S + a * B + q * N) / r).

      Lemma eval_S3_eq : eval S3 = eval_pre_S3 mod (r * r ^ Z.of_nat R_numlimbs).
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        unfold S3, S2, S1.
        autorewrite with push_mont_eval push_Zof_nat; [].
        rewrite !Z.pow_succ_r, <- ?Z.mul_assoc by lia.
        rewrite Z.mod_pull_div by Z.zero_bounds.
        do 2 f_equal; nia.
      Qed.

      Lemma pre_S3_bound
        : eval S < eval N + eval B
          -> eval_pre_S3 < eval N + eval B.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big.
        assert (Hmod : forall a b, 0 < b -> a mod b <= b - 1)
          by (intros x y; pose proof (Z_mod_lt x y); lia).
        intro HS.
        eapply Z.le_lt_trans.
        { transitivity ((N+B-1 + (r-1)*B + (r-1)*N) / r);
            [ | set_evars; ring_simplify_subterms; subst_evars; reflexivity ].
          Z.peel_le; repeat apply Z.add_le_mono; repeat apply Z.mul_le_mono_nonneg; try lia;
            repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
              autorewrite with push_mont_eval;
              try Z.zero_bounds;
              auto with lia. }
        rewrite (Z.mul_comm _ r), <- Z.add_sub_assoc, <- Z.add_opp_r, !Z.div_add_l' by lia.
        autorewrite with zsimplify.
        simpl; lia.
      Qed.

      Lemma pre_S3_nonneg : 0 <= eval_pre_S3.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg lgr_big.
        clear -N_nz B_bounds small_B partition_Proper r_big' small_A small_S S_nonneg.
        repeat autounfold with word_by_word_montgomery; rewrite ?Z.mul_split_mod;
          autorewrite with push_mont_eval; [].
        rewrite ?Npos_correct; Z.zero_bounds; lia.
      Qed.

      Lemma small_A'
        : small A'.
      Proof using small_A lgr_big. repeat autounfold with word_by_word_montgomery; t_small. Qed.

      Lemma small_S3
        : small S3.
      Proof using small_A small_S small_N N_lt_R N_nz B_bounds small_B lgr_big.
        clear -small_A small_S small_N N_lt_R N_nz B_bounds small_B partition_Proper r_big'.
        repeat autounfold with word_by_word_montgomery; t_small.
      Qed.

      Lemma S3_nonneg : 0 <= eval S3.
      Proof using small_A small_S small_B B_bounds N_nz N_lt_R small_N lgr_big.
        clear -small_A small_S r_big' partition_Proper small_B B_bounds N_nz N_lt_R small_N lgr_big sub_then_maybe_add.
        rewrite eval_S3_eq; Z.zero_bounds.
      Qed.

      Lemma S3_bound
        : eval S < eval N + eval B
          -> eval S3 < eval N + eval B.
      Proof using N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big.
        clear -N_nz B_bounds small_B small_A small_S S_nonneg B_bounds N_nz N_lt_R small_N lgr_big partition_Proper r_big' sub_then_maybe_add.
        rewrite eval_S3_eq.
        intro H; pose proof (pre_S3_bound H); pose proof pre_S3_nonneg.
        subst R.
        rewrite Z.mod_small by nia.
        assumption.
      Qed.

      Lemma S1_eq : eval S1 = S + a*B.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper.
        cbv [S1 a A'].
        repeat autorewrite with push_mont_eval.
        reflexivity.
      Qed.

      Lemma S2_mod_r_helper : (S + a*B + q * N) mod r = 0.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct.
        cbv [S2 q s]; autorewrite with push_mont_eval; rewrite S1_eq.
        assert (r > 0) by lia.
        assert (Hr : (-(1 mod r)) mod r = r - 1 /\ (-(1)) mod r = r - 1).
        { destruct (Z.eq_dec r 1) as [H'|H'].
          { rewrite H'; split; reflexivity. }
          { rewrite !Z_mod_nz_opp_full; rewrite ?Z.mod_mod; Z.rewrite_mod_small; [ split; reflexivity | lia.. ]. } }
        autorewrite with pull_Zmod.
        replace 0 with (0 mod r) by apply Zmod_0_l.
        pose (Z.to_pos r) as r'.
        replace r with (Z.pos r') by (subst r'; rewrite Z2Pos.id; lia).
        eapply F.eq_of_Z_iff.
        rewrite Z.mul_split_mod.
        repeat rewrite ?F.of_Z_add, ?F.of_Z_mul, <-?F.of_Z_mod.
        rewrite <-!Algebra.Hierarchy.associative.
        replace ((F.of_Z r' k * F.of_Z r' (eval N))%F) with (F.opp (m:=r') F.one).
        { cbv [F.of_Z F.add]; simpl.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ].
          simpl.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), Z.mul_sub_distr_l.
          push_Zmod; pull_Zmod.
          apply (f_equal2 Z.modulo); lia. }
        { rewrite <- F.of_Z_mul.
          rewrite F.of_Z_mod.
          subst r'; rewrite Z2Pos.id by lia.
          rewrite k_correct.
          cbv [F.of_Z F.add F.opp F.one]; simpl.
          change (-(1)) with (-1) in *.
          apply path_sig_hprop; [ intro; exact HProp.allpath_hprop | ]; simpl.
          rewrite Z2Pos.id by lia.
          rewrite (proj1 Hr), (proj2 Hr); Z.rewrite_mod_small; reflexivity. }
      Qed.

      Lemma pre_S3_mod_N
        : eval_pre_S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct sub_then_maybe_add.
        pose proof fun a => Z.div_to_inv_modulo N a r ri ltac:(lia) ri_correct as HH;
                              cbv [Z.equiv_modulo] in HH; rewrite HH; clear HH.
        etransitivity; [rewrite (fun a => Z.mul_mod_l a ri N)|
                        rewrite (fun a => Z.mul_mod_l a ri N); reflexivity].
        rewrite S2_mod_r_helper.
        push_Zmod; pull_Zmod; autorewrite with zsimplify_const.
        reflexivity.
      Qed.

      Lemma S3_mod_N
            (Hbound : eval S < eval N + eval B)
        : S3 mod N = (S + a*B)*ri mod N.
      Proof using B_bounds R_numlimbs_nz lgr_big small_A small_B small_S k_correct ri_correct small_N N_lt_R N_nz S_nonneg.
        clear -B_bounds R_numlimbs_nz lgr_big small_A small_B small_S r_big' partition_Proper k_correct ri_correct N_nz N_lt_R small_N sub_then_maybe_add Hbound S_nonneg.
        rewrite eval_S3_eq.
        pose proof (pre_S3_bound Hbound); pose proof pre_S3_nonneg.
        rewrite (Z.mod_small _ (r * _)) by (subst R; nia).
        apply pre_S3_mod_N.
      Qed.
    End Iteration_proofs.

    Section redc_proofs.
      Local Notation redc_body := (@redc_body B k).
      Local Notation redc_loop := (@redc_loop B k).
      Local Notation pre_redc A := (@pre_redc _ A B k).
      Local Notation redc A := (@redc _ A B k).

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
        Proof using S_bound small_A small_S lgr_big. destruct A_S; apply small_A'; assumption. Qed.
        Lemma small_snd_redc_body : small (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound B_bounds N_nz N_lt_R.
          destruct A_S; unfold redc_body; apply small_S3; assumption.
        Qed.
        Lemma snd_redc_body_nonneg : 0 <= eval (snd (redc_body A_S)).
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          destruct A_S; apply S3_nonneg; assumption.
        Qed.

        Lemma snd_redc_body_mod_N
          : (eval (snd (redc_body A_S))) mod (eval N) = (eval S + a*eval B)*ri mod (eval N).
        Proof using small_S small_N small_B small_A ri_correct lgr_big k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A ri_correct k_correct S_bound R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add r_big' partition_Proper.
          destruct A_S; apply S3_mod_N; auto; lia.
        Qed.

        Lemma fst_redc_body
          : (eval (fst (redc_body A_S))) = eval (fst A_S) / r.
        Proof using small_S small_A S_bound lgr_big.
          destruct A_S; simpl; repeat autounfold with word_by_word_montgomery; simpl.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma fst_redc_body_mod_N
          : (eval (fst (redc_body A_S))) mod (eval N) = ((eval (fst A_S) - a)*ri) mod (eval N).
        Proof using small_S small_A ri_correct lgr_big S_bound.
          clear R_numlimbs_nz.
          rewrite fst_redc_body.
          etransitivity; [ eapply Z.div_to_inv_modulo; try eassumption; lia | ].
          unfold a, A_a, A.
          autorewrite with push_mont_eval.
          reflexivity.
        Qed.

        Lemma redc_body_bound
          : eval S < eval N + eval B
            -> eval (snd (redc_body A_S)) < eval N + eval B.
        Proof using small_S small_N small_B small_A lgr_big S_bound N_nz N_lt_R B_bounds.
          clear -small_S small_N small_B small_A S_bound N_nz N_lt_R B_bounds r_big' partition_Proper sub_then_maybe_add.
          destruct A_S; apply S3_bound; unfold S in *; cbn [snd] in *; try assumption; try lia.
        Qed.
      End body.

      Local Arguments Z.pow !_ !_.
      Local Arguments Z.of_nat !_.
      Local Ltac induction_loop count IHcount
        := induction count as [|count IHcount]; intros; cbn [redc_loop nat_rect] in *; [ | (*rewrite redc_loop_comm_body in * *) ].
      Lemma redc_loop_good count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : (small (fst (redc_loop count A_S)) /\ small (snd (redc_loop count A_S)))
          /\ 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
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
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

      Lemma redc_loop_bound count A_S
            (Hsmall : small (fst A_S) /\ small (snd A_S))
            (Hbound : 0 <= eval (snd A_S) < eval N + eval B)
        : 0 <= eval (snd (redc_loop count A_S)) < eval N + eval B.
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds. apply redc_loop_good; assumption. Qed.

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
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound.
        cbv [redc_loop]; induction_loop count IHcount.
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
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds ri_correct.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add Hsmall Hbound ri_correct.
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
      Proof using small_N small_B ri_correct lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds k_correct.
        clear -small_N small_B ri_correct r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds sub_then_maybe_add k_correct Hsmall Hbound.
        cbv [redc_loop].
        induction_loop count IHcount.
        { simpl; autorewrite with zsimplify; reflexivity. }
        { rewrite IHcount by handle_IH_small.
          push_Zmod; rewrite snd_redc_body_mod_N, fst_redc_body by handle_IH_small; pull_Zmod.
          autorewrite with push_mont_eval; [].
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
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma small_pre_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : small (pre_redc A).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds sub_then_maybe_add small_A.
        unfold pre_redc.
        apply redc_loop_good; simpl; autorewrite with push_mont_eval;
          rewrite ?Npos_correct; auto; lia.
      Qed.

      Lemma pre_redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (pre_redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct.
        clear -small_N small_B r_big' partition_Proper lgr_big N_nz N_lt_R B_bounds R_numlimbs_nz ri_correct k_correct sub_then_maybe_add small_A A_bound.
        unfold pre_redc.
        rewrite snd_redc_loop_mod_N; cbn [fst snd];
          autorewrite with push_mont_eval zsimplify;
          [ | rewrite ?Npos_correct; auto; lia.. ].
        Z.rewrite_mod_small.
        reflexivity.
      Qed.

      Lemma redc_mod_N A_numlimbs (A : T A_numlimbs) (small_A : small A) (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : (eval (redc A)) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
      Proof using small_N small_B ri_correct lgr_big k_correct R_numlimbs_nz N_nz N_lt_R B_bounds.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        autorewrite with push_mont_eval; [].
        break_innermost_match;
          try rewrite Z.add_opp_r, Zminus_mod, Z_mod_same_full;
          autorewrite with zsimplify_fast;
          apply pre_redc_mod_N; auto.
      Qed.

      Lemma redc_bound_tight A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : 0 <= eval (redc A) < eval N + eval B + (if eval N <=? eval (pre_redc A) then -eval N else 0).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds r_big' partition_Proper small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Lemma redc_bound_N A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
        : eval B < eval N -> 0 <= eval (redc A) < eval N.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Lemma redc_bound A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : 0 <= eval (redc A) < R.
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        rewrite eval_conditional_sub by t_small.
        break_innermost_match; Z.ltb_to_lt; try lia.
      Qed.

      Lemma small_redc A_numlimbs (A : T A_numlimbs)
            (small_A : small A)
            (A_bound : 0 <= eval A < r ^ Z.of_nat A_numlimbs)
        : small (redc A).
      Proof using small_N small_B lgr_big R_numlimbs_nz N_nz N_lt_R B_bounds.
        clear -small_N small_B r_big' partition_Proper R_numlimbs_nz N_nz N_lt_R B_bounds small_A sub_then_maybe_add A_bound.
        pose proof (@small_pre_redc _ A small_A).
        pose proof (@pre_redc_bound _ A small_A).
        unfold redc.
        apply small_conditional_sub; [ apply small_pre_redc | .. ]; auto; lia.
      Qed.
    End redc_proofs.

    Section add_sub.
      Context (Av Bv : T R_numlimbs)
              (small_Av : small Av)
              (small_Bv : small Bv)
              (Av_bound : 0 <= eval Av < eval N)
              (Bv_bound : 0 <= eval Bv < eval N).

      Local Ltac do_clear :=
        clear dependent B; clear dependent k; clear dependent ri.

      Lemma small_add : small (add Av Bv).
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; t_small.
      Qed.
      Lemma small_sub : small (sub Av Bv).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Bv_bound Av_bound. unfold sub; t_small. Qed.
      Lemma small_opp : small (opp Av).
      Proof using small_N small_Bv small_Av partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R Av_bound. unfold opp, sub; t_small. Qed.

      Lemma eval_add : eval (add Av Bv) = eval Av + eval Bv + (if (eval N <=? eval Av + eval Bv) then -eval N else 0).
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        clear -small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound partition_Proper r_big' small_N ri k R_numlimbs_nz N_nz B_bounds B sub_then_maybe_add.
        unfold add; autorewrite with push_mont_eval; reflexivity.
      Qed.
      Lemma eval_sub : eval (sub Av Bv) = eval Av - eval Bv + (if (eval Av - eval Bv <? 0) then eval N else 0).
      Proof using small_Bv small_Av Bv_bound Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. unfold sub; autorewrite with push_mont_eval; reflexivity. Qed.
      Lemma eval_opp : eval (opp Av) = (if (eval Av =? 0) then 0 else eval N) - eval Av.
      Proof using small_Av Av_bound small_N partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R.
        clear -Av_bound N_nz small_Av partition_Proper r_big' small_N lgr_big R_numlimbs_nz N_nz N_lt_R.
        unfold opp, sub; autorewrite with push_mont_eval.
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
      Proof using small_Bv small_Av lgr_big N_lt_R Bv_bound Av_bound small_N ri k R_numlimbs_nz N_nz B_bounds B.
        generalize eval_add; clear. t_mod_N.
      Qed.
      Lemma eval_sub_mod_N : eval (sub Av Bv) mod eval N = (eval Av - eval Bv) mod eval N.
      Proof using small_Bv small_Av Bv_bound Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_sub; clear. t_mod_N. Qed.
      Lemma eval_opp_mod_N : eval (opp Av) mod eval N = (-eval Av) mod eval N.
      Proof using small_Av Av_bound small_N r_big' partition_Proper lgr_big R_numlimbs_nz N_nz N_lt_R. generalize eval_opp; clear. t_mod_N. Qed.

      Lemma add_bound : 0 <= eval (add Av Bv) < eval N.
      Proof using small_Bv small_Av lgr_big R_numlimbs_nz N_lt_R Bv_bound Av_bound small_N ri k N_nz B_bounds B.
        generalize eval_add; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma sub_bound : 0 <= eval (sub Av Bv) < eval N.
      Proof using small_Bv small_Av R_numlimbs_nz Bv_bound Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        generalize eval_sub; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
      Lemma opp_bound : 0 <= eval (opp Av) < eval N.
      Proof using small_Av R_numlimbs_nz Av_bound small_N r_big' partition_Proper lgr_big N_nz N_lt_R.
        clear Bv small_Bv Bv_bound.
        generalize eval_opp; break_innermost_match; Z.ltb_to_lt; lia.
      Qed.
    End add_sub.
  End with_args.

  Section modops.
    Context (bitwidth : Z)
            (n : nat)
            (m : Z).
    Let r := 2^bitwidth.
    Local Notation weight := (uweight bitwidth).
    Local Notation eval := (@eval bitwidth n).
    Let m_enc := Partition.partition weight n m.
    Local Coercion Z.of_nat : nat >-> Z.
    Context (r' : Z)
            (m' : Z)
            (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bitwidth_big : 0 < bitwidth)
            (m_big : 1 < m)
            (n_nz : n <> 0%nat)
            (m_small : m < r^n).

    Local Notation wprops := (@uwprops bitwidth bitwidth_big).
    Local Notation small := (@small bitwidth n).

    Local Hint Immediate (wprops) : core.
    Local Hint Immediate (weight_0 wprops) : core.
    Local Hint Immediate (weight_positive wprops) : core.
    Local Hint Immediate (weight_multiples wprops) : core.
    Local Hint Immediate (weight_divides wprops) : core.

    Local Lemma r'_correct_alt : ((r mod m) * (r' mod m)) mod m = 1.
    Proof using r'_correct. pull_Zmod; apply r'_correct. Qed.

    Local Lemma m_enc_correct_montgomery : m = eval m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [eval m_enc]; autorewrite with push_eval; auto.
      rewrite uweight_eq_alt by lia.
      Z.rewrite_mod_small; reflexivity.
    Qed.
    Local Lemma r'_pow_correct : (r'^n * r^n) mod (eval m_enc) = 1.
    Proof using r'_correct m_small m_big bitwidth_big.
      clear -r'_correct m_small m_big bitwidth_big.
      rewrite <- Z.pow_mul_l, Z.mod_pow_full, ?(Z.mul_comm r'), <- m_enc_correct_montgomery, r'_correct.
      autorewrite with zsimplify_const; auto with lia.
      Z.rewrite_mod_small; lia.
    Qed.
    Local Lemma small_m_enc : small m_enc.
    Proof using m_small m_big bitwidth_big.
      clear -m_small m_big bitwidth_big.
      cbv [m_enc small eval]; autorewrite with push_eval; auto.
      rewrite uweight_eq_alt by lia.
      Z.rewrite_mod_small; reflexivity.
    Qed.

    Local Ltac t_fin :=
      repeat match goal with
             | _ => assumption
             | [ |- ?x = ?x ] => reflexivity
             | [ |- and _ _ ] => split
             | _ => rewrite <- !m_enc_correct_montgomery
             | _ => rewrite !r'_correct
             | _ => rewrite !Z.mod_1_l by assumption; reflexivity
             | _ => rewrite !(Z.mul_comm m' m)
             | _ => lia
             | _ => exact small_m_enc
             | [ H : small ?x |- context[eval ?x] ]
               => rewrite H; cbv [eval]; rewrite eval_partition by auto
             | [ |- context[weight _] ] => rewrite uweight_eq_alt by auto with lia
             | _=> progress Z.rewrite_mod_small
             | _ => progress Z.zero_bounds
             | [ |- _ mod ?x < ?x ] => apply Z.mod_pos_bound
             end.

    Definition mulmod (a b : list Z) : list Z := @redc bitwidth n m_enc n a b m'.
    Definition squaremod (a : list Z) : list Z := mulmod a a.
    Definition addmod (a b : list Z) : list Z := @add bitwidth n m_enc a b.
    Definition submod (a b : list Z) : list Z := @sub bitwidth n m_enc a b.
    Definition oppmod (a : list Z) : list Z := @opp bitwidth n m_enc a.
    Definition nonzeromod (a : list Z) : Z := @nonzero a.
    Definition to_bytesmod (a : list Z) : list Z := @to_bytesmod bitwidth 1 (2^Z.log2_up m) n a.

    Definition valid (a : list Z) := small a /\ 0 <= eval a < m.

    Lemma mulmod_correct0
      : forall a b : list Z,
        small a -> small b
        -> small (mulmod a b)
          /\ (eval b < m -> 0 <= eval (mulmod a b) < m)
          /\ (eval (mulmod a b) mod m = (eval a * eval b * r'^n) mod m).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a b Ha Hb; repeat apply conj; cbv [small mulmod eval];
        [ eapply small_redc
        | rewrite m_enc_correct_montgomery; eapply redc_bound_N
        | rewrite !m_enc_correct_montgomery; eapply redc_mod_N ];
        t_fin.
    Qed.

    Definition onemod : list Z := Partition.partition weight n 1.

    Definition onemod_correct : eval onemod = 1 /\ valid onemod.
    Proof using n_nz m_big bitwidth_big.
      clear -n_nz m_big bitwidth_big.
      cbv [valid small onemod eval]; autorewrite with push_eval; t_fin.
    Qed.

    Lemma eval_onemod : eval onemod = 1.
    Proof. apply onemod_correct. Qed.

    Definition R2mod : list Z := Partition.partition weight n ((r^n * r^n) mod m).

    Definition R2mod_correct : eval R2mod mod m = (r^n*r^n) mod m /\ valid R2mod.
    Proof using n_nz m_small m_big m'_correct bitwidth_big.
      clear -n_nz m_small m_big m'_correct bitwidth_big.
      cbv [valid small R2mod eval]; autorewrite with push_eval; t_fin;
        rewrite !(Z.mod_small (_ mod m)) by (Z.div_mod_to_quot_rem; subst r; lia);
        t_fin.
    Qed.

    Lemma eval_R2mod : eval R2mod mod m = (r^n*r^n) mod m.
    Proof using n_nz m_small m_big m'_correct bitwidth_big. apply R2mod_correct. Qed.

    Definition from_montgomerymod (v : list Z) : list Z
      := mulmod v onemod.

    Lemma from_montgomerymod_correct (v : list Z)
      : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m
                  /\ valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      clear -r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intro Hv; cbv [from_montgomerymod valid] in *; destruct_head'_and.
      replace (eval v * r'^n) with (eval v * eval onemod * r'^n) by (rewrite (proj1 onemod_correct); lia).
      repeat apply conj; apply mulmod_correct0; auto; try apply onemod_correct; rewrite (proj1 onemod_correct); lia.
    Qed.

    Lemma eval_from_montgomerymod (v : list Z) : valid v -> eval (from_montgomerymod v) mod m = (eval v * r'^n) mod m.
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.
    Lemma valid_from_montgomerymod (v : list Z)
      : valid v -> valid (from_montgomerymod v).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros; apply from_montgomerymod_correct; assumption.
    Qed.

    Lemma mulmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (mulmod a b)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (mulmod a b)).
    Proof using r'_correct r' n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          try apply mulmod_correct0; cbv [valid] in *; destruct_head'_and; auto; [].
      rewrite !Z.mul_assoc.
      apply Z.mul_mod_Proper; [ | reflexivity ].
      cbv [Z.equiv_modulo]; etransitivity; [ apply mulmod_correct0 | apply f_equal2; lia ]; auto.
    Qed.

    Lemma eval_mulmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (mulmod a b)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod b)) mod m).
    Proof. apply mulmod_correct. Qed.

    Lemma squaremod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (squaremod a)) mod m
                                            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (squaremod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros; cbv [squaremod]; apply mulmod_correct; assumption.
    Qed.

    Lemma eval_squaremod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (squaremod a)) mod m
            = (eval (from_montgomerymod a) * eval (from_montgomerymod a)) mod m).
    Proof. apply squaremod_correct. Qed.

    Local Ltac t_valid_side :=
      repeat first [ solve [ auto ]
                   | apply R2mod_correct
                   | apply mulmod_correct ].

    Definition to_montgomerymod (v : list Z) : list Z
      := mulmod v R2mod.

    Lemma to_montgomerymod_correct
      : (forall v (_ : valid v),
            eval (from_montgomerymod (to_montgomerymod v)) mod m
            = eval v mod m)
        /\ (forall v (_ : valid v), valid (to_montgomerymod v)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros v ?; cbv [to_montgomerymod]; [ | t_valid_side ].
      repeat first [ reflexivity
                   | rewrite !eval_mulmod by t_valid_side
                   | rewrite !eval_from_montgomerymod by t_valid_side
                   | rewrite !eval_R2mod by t_valid_side
                   | rewrite r'_correct_alt
                   | rewrite Z.mul_1_r
                   | rewrite Z.mod_mod by lia
                   | rewrite (Z.mul_comm (r' mod _) (r mod _))
                   | progress push_Zmod
                   | progress (pull_Zmod; rewrite Z.mul_1_r; push_Zmod)
                   | progress (pull_Zmod; rewrite Z.pow_1_l by lia; push_Zmod)
                   | progress (pull_Zmod; rewrite <- !Z.mul_assoc, <- !Z.pow_mul_l; push_Zmod) ].
    Qed.

    Lemma eval_to_montgomerymod
      : forall v (_ : valid v),
        eval (from_montgomerymod (to_montgomerymod v)) mod m
        = eval v mod m.
    Proof. apply to_montgomerymod_correct. Qed.

    Definition encodemod (v : Z) : list Z
      := to_montgomerymod (Partition.partition weight n v).

    Local Ltac t_valid v :=
      cbv [valid]; repeat apply conj;
      auto; cbv [small eval]; autorewrite with push_eval; auto;
      rewrite ?uweight_eq_alt by lia;
      Z.rewrite_mod_small;
      rewrite ?(Z.mod_small (_ mod m)) by (subst r; Z.div_mod_to_quot_rem; lia);
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia);
      try apply Z.mod_pos_bound; subst r; try lia; try reflexivity.
    Lemma encodemod_correct
      : (forall v, 0 <= v < m -> eval (from_montgomerymod (encodemod v)) mod m = v mod m)
        /\ (forall v, 0 <= v < m -> valid (encodemod v)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      split; intros v ?; cbv [encodemod];
        [ rewrite eval_to_montgomerymod | apply to_montgomerymod_correct ];
        [ | now t_valid v.. ].
      cbv [eval]; autorewrite with push_eval; auto.
      rewrite ?uweight_eq_alt by lia.
      rewrite ?(Z.mod_small v) by (subst r; Z.div_mod_to_quot_rem; lia).
      reflexivity.
    Qed.

    Lemma eval_encodemod
      : (forall v, 0 <= v < m
                   -> eval (from_montgomerymod (encodemod v)) mod m = v mod m).
    Proof. apply encodemod_correct. Qed.

    Lemma addmod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (addmod a b)) mod m
                                            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (addmod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid addmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_add || eapply add_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_add by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_addmod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (addmod a b)) mod m
            = (eval (from_montgomerymod a) + eval (from_montgomerymod b)) mod m).
    Proof. apply addmod_correct. Qed.

    Lemma submod_correct
      : (forall a (_ : valid a) b (_ : valid b), eval (from_montgomerymod (submod a b)) mod m
                                            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m)
        /\ (forall a (_ : valid a) b (_ : valid b), valid (submod a b)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid submod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_sub || eapply sub_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_sub by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_submod
      : (forall a (_ : valid a) b (_ : valid b),
            eval (from_montgomerymod (submod a b)) mod m
            = (eval (from_montgomerymod a) - eval (from_montgomerymod b)) mod m).
    Proof. apply submod_correct. Qed.

    Lemma oppmod_correct
      : (forall a (_ : valid a), eval (from_montgomerymod (oppmod a)) mod m
                            = (-eval (from_montgomerymod a)) mod m)
        /\ (forall a (_ : valid a), valid (oppmod a)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      repeat apply conj; intros;
        push_Zmod; rewrite ?eval_from_montgomerymod; pull_Zmod; repeat apply conj;
          cbv [valid oppmod] in *; destruct_head'_and; auto;
            try rewrite m_enc_correct_montgomery;
            try (eapply small_opp || eapply opp_bound);
            cbv [small]; rewrite <- ?m_enc_correct_montgomery;
              eauto with lia; [ ].
      push_Zmod; erewrite eval_opp by (cbv [small]; rewrite <- ?m_enc_correct_montgomery; eauto with lia); pull_Zmod; rewrite <- ?m_enc_correct_montgomery.
      break_innermost_match; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; apply f_equal2; nia.
    Qed.

    Lemma eval_oppmod
      : (forall a (_ : valid a),
            eval (from_montgomerymod (oppmod a)) mod m
            = (-eval (from_montgomerymod a)) mod m).
    Proof. apply oppmod_correct. Qed.

    Lemma nonzeromod_correct
      : (forall a (_ : valid a), (nonzeromod a = 0) <-> ((eval (from_montgomerymod a)) mod m = 0)).
    Proof using r'_correct n_nz m_small m_big m'_correct bitwidth_big.
      intros a Ha; rewrite eval_from_montgomerymod by assumption.
      cbv [nonzeromod valid] in *; destruct_head'_and.
      rewrite eval_nonzero; try eassumption; [ | subst r; apply conj; try eassumption; lia.. ].
      split; intro H'; [ rewrite H'; autorewrite with zsimplify_const; reflexivity | ].
      assert (H'' : ((eval a * r'^n) * r^n) mod m = 0)
        by (revert H'; push_Zmod; intro H'; rewrite H'; autorewrite with zsimplify_const; reflexivity).
      rewrite <- Z.mul_assoc in H''.
      autorewrite with pull_Zpow push_Zmod in H''.
      rewrite (Z.mul_comm r' r), r'_correct in H''.
      autorewrite with zsimplify_const pull_Zmod in H''; [ | lia.. ].
      clear H'.
      generalize dependent (eval a); clear.
      intros z ???.
      assert (z / m = 0) by (Z.div_mod_to_quot_rem; nia).
      Z.div_mod_to_quot_rem; nia.
    Qed.

    Lemma to_bytesmod_correct
      : (forall a (_ : valid a), Positional.eval (uweight 8) (bytes_n (2^Z.log2_up m)) (to_bytesmod a)
                                 = eval a mod m)
        /\ (forall a (_ : valid a), to_bytesmod a = Partition.partition (uweight 8) (bytes_n (2^Z.log2_up m)) (eval a mod m)).
    Proof using m_big n_nz m_small bitwidth_big.
      clear -m_big n_nz m_small bitwidth_big.
      pose proof (Z.log2_up_le_full m).
      generalize (@length_small bitwidth n);
        cbv [valid small to_bytesmod eval]; split; intros; (etransitivity; [ apply eval_to_bytesmod | ]);
          fold weight in *; fold (uweight 8) in *; subst r;
          try solve [ intuition eauto with lia ].
      all: repeat first [ rewrite uweight_eq_alt by lia
                        | lia
                        | reflexivity
                        | progress Z.rewrite_mod_small ].
    Qed.

    Lemma eval_to_bytesmod
      : (forall a (_ : valid a),
            Positional.eval (uweight 8) (bytes_n (2^Z.log2_up m)) (to_bytesmod a)
            = eval a mod m).
    Proof. apply to_bytesmod_correct. Qed.
  End modops.
End WordByWordMontgomery.
