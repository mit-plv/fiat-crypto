(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Proofs.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Section WordByWordMontgomery.
  (** XXX TODO: pick better names for things like [R_numlimbs] *)
  Context (r : positive)
          (R_numlimbs : nat).
  Local Notation small := (@small (Z.pos r)).
  Local Notation eval := (@eval (Z.pos r)).
  Local Notation addT' := (@MontgomeryAPI.add_S1 (Z.pos r)).
  Local Notation addT := (@MontgomeryAPI.add (Z.pos r)).
  Local Notation scmul := (@scmul (Z.pos r)).
  Local Notation eval_zero := (@eval_zero (Z.pos r)).
  Local Notation small_zero := (@small_zero r (Zorder.Zgt_pos_0 _)).
  Local Notation small_scmul := (fun n a v _ _ _ => @small_scmul r (Zorder.Zgt_pos_0 _) n a v).
  Local Notation eval_join0 := (@eval_zero (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_div := (@eval_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_mod := (@eval_mod (Z.pos r)).
  Local Notation small_div := (@small_div (Z.pos r)).
  Local Notation eval_scmul := (fun n a v smallv abound vbound => @eval_scmul (Z.pos r) (Zorder.Zgt_pos_0 _) n a v smallv abound).
  Local Notation eval_addT := (@eval_add_same (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_addT' := (@eval_add_S1 (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation drop_high := (@drop_high (S R_numlimbs)).
  Local Notation small_drop_high := (@small_drop_high (Z.pos r) (S R_numlimbs)).
  Context (A_numlimbs : nat)
          (N : T R_numlimbs)
          (A : T A_numlimbs)
          (B : T R_numlimbs)
          (k : Z).
  Context ri
          (r_big : r > 1)
          (small_A : small A)
          (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
          (small_N : small N)
          (small_B : small B)
          (N_nonzero : eval N <> 0)
          (N_mask : Tuple.map (Z.land (Z.pos r - 1)) N = N)
          (k_correct : k * eval N mod r = (-1) mod r).
  Let R : positive := match (Z.pos r ^ Z.of_nat R_numlimbs)%Z with
                      | Z.pos R => R
                      | _ => 1%positive
                      end.
  Let Npos : positive := match eval N with
                         | Z.pos N => N
                         | _ => 1%positive
                         end.
  Local Lemma R_correct : Z.pos R = Z.pos r ^ Z.of_nat R_numlimbs.
  Proof.
    assert (0 < r^Z.of_nat R_numlimbs) by (apply Z.pow_pos_nonneg; lia).
    subst R; destruct (Z.pos r ^ Z.of_nat R_numlimbs) eqn:?; [ | reflexivity | ];
      lia.
  Qed.
  Local Lemma small_addT : forall n a b, small a -> small b -> small (@addT n a b).
  Proof.
    intros; apply MontgomeryAPI.small_add; auto; lia.
  Qed.
  Local Lemma small_addT' : forall n a b, small a -> small b -> small (@addT' n a b).
  Proof.
    intros; apply MontgomeryAPI.small_add_S1; auto; lia.
  Qed.

  Local Notation conditional_sub_cps := (fun V : T (S R_numlimbs) => @conditional_sub_cps (Z.pos r) _ V N _).
  Local Notation conditional_sub := (fun V : T (S R_numlimbs) => @conditional_sub (Z.pos r) _ V N).
  Local Notation eval_conditional_sub' := (fun V small_V V_bound => @eval_conditional_sub (Z.pos r) (Zorder.Zgt_pos_0 _) _  V N small_V small_N V_bound).

  Local Lemma eval_conditional_sub
    : forall v, small v -> 0 <= eval v < eval N + R -> eval (conditional_sub v) = eval v + if eval N <=? eval v then -eval N else 0.
  Proof. rewrite R_correct; exact eval_conditional_sub'. Qed.
  Local Notation small_conditional_sub' := (fun V small_V V_bound => @small_conditional_sub (Z.pos r) (Zorder.Zgt_pos_0 _) _ V N small_V small_N V_bound).
  Local Lemma small_conditional_sub
    : forall v : T (S R_numlimbs), small v -> 0 <= eval v < eval N + R -> small (conditional_sub v).
  Proof. rewrite R_correct; exact small_conditional_sub'. Qed.

  Local Lemma A_bound : 0 <= eval A < Z.pos r ^ Z.of_nat A_numlimbs.
  Proof. apply eval_small; auto; lia. Qed.
  Local Lemma B_bound' : 0 <= eval B < r^Z.of_nat R_numlimbs.
  Proof. apply eval_small; auto; lia. Qed.
  Local Lemma N_bound' : 0 <= eval N < r^Z.of_nat R_numlimbs.
  Proof. apply eval_small; auto; lia. Qed.
  Local Lemma N_bound : 0 < eval N < r^Z.of_nat R_numlimbs.
  Proof. pose proof N_bound'; lia. Qed.
  Local Lemma Npos_correct: eval N = Z.pos Npos.
  Proof. pose proof N_bound; subst Npos; destruct (eval N); [ | reflexivity | ]; lia. Qed.
  Local Lemma N_lt_R : eval N < R.
  Proof. rewrite R_correct; apply N_bound. Qed.
  Local Lemma B_bound : 0 <= eval B < R.
  Proof. rewrite R_correct; apply B_bound'. Qed.
  Local Lemma eval_drop_high : forall v, small v -> eval (drop_high v) = eval v mod (r * r^Z.of_nat R_numlimbs).
  Proof.
    intros; erewrite eval_drop_high by (eassumption || lia).
    f_equal; unfold uweight.
    rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity.
  Qed.

  Local Notation redc_body_no_cps := (@redc_body_no_cps r R_numlimbs N).
  Local Notation redc_body_cps := (@redc_body_cps r R_numlimbs N).
  Local Notation redc_body := (@redc_body r R_numlimbs N).
  Local Notation redc_loop_no_cps := (@redc_loop_no_cps r R_numlimbs N B k).
  Local Notation redc_loop_cps := (@redc_loop_cps r R_numlimbs N B k).
  Local Notation redc_loop := (@redc_loop r R_numlimbs N B k).
  Local Notation pre_redc_no_cps := (@pre_redc_no_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation pre_redc_cps := (@pre_redc_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation pre_redc := (@pre_redc r R_numlimbs N A_numlimbs A B k).
  Local Notation redc_no_cps := (@redc_no_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation redc_cps := (@redc_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation redc := (@redc r R_numlimbs N A_numlimbs A B k).

  Definition redc_no_cps_bound : 0 <= eval redc_no_cps < R
    := @redc_bound T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero small_zero eval_div eval_mod small_div (@scmul) eval_scmul small_scmul (@addT) eval_addT small_addT (@addT') eval_addT' small_addT' drop_high eval_drop_high small_drop_high N Npos Npos_correct small_N N_lt_R conditional_sub eval_conditional_sub B B_bound small_B ri k A_numlimbs A small_A A_bound.
  Definition redc_no_cps_bound_N : eval B < eval N -> 0 <= eval redc_no_cps < eval N
    := @redc_bound_N T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero small_zero eval_div eval_mod small_div (@scmul) eval_scmul small_scmul (@addT) eval_addT small_addT (@addT') eval_addT' small_addT' drop_high eval_drop_high small_drop_high N Npos Npos_correct small_N N_lt_R conditional_sub eval_conditional_sub B B_bound small_B ri k A_numlimbs A small_A.
  Definition redc_no_cps_mod_N
    : (eval redc_no_cps) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N)
    := @redc_mod_N T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero small_zero eval_div eval_mod small_div (@scmul) eval_scmul small_scmul (@addT) eval_addT small_addT (@addT') eval_addT' small_addT' drop_high eval_drop_high small_drop_high N Npos Npos_correct small_N N_lt_R conditional_sub eval_conditional_sub B B_bound small_B ri ri_correct k k_correct A_numlimbs A small_A A_bound.
  Definition small_redc_no_cps
    : small redc_no_cps
    := @small_redc T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero small_zero eval_div eval_mod small_div (@scmul) eval_scmul small_scmul (@addT) eval_addT small_addT (@addT') eval_addT' small_addT' drop_high eval_drop_high small_drop_high N Npos Npos_correct small_N N_lt_R conditional_sub small_conditional_sub B B_bound small_B ri k A_numlimbs A small_A A_bound.

  Lemma redc_body_cps_id pred_A_numlimbs (A' : T (S pred_A_numlimbs)) (S' : T (S R_numlimbs)) {cpsT} f
    : @redc_body_cps pred_A_numlimbs A' B k S' cpsT f = f (redc_body A' B k S').
  Proof.
    unfold redc_body, redc_body_cps, LetIn.Let_In.
    repeat first [ reflexivity
                 | break_innermost_match_step
                 | progress autorewrite with uncps ].
  Qed.

  Lemma redc_loop_cps_id (count : nat) (A_S : T count * T (S R_numlimbs)) {cpsT} f
    : @redc_loop_cps cpsT count f A_S = f (redc_loop count A_S).
  Proof.
    unfold redc_loop.
    revert A_S f.
    induction count as [|count IHcount].
    { reflexivity. }
    { intros [A' S']; simpl; intros.
      etransitivity; rewrite @redc_body_cps_id; [ rewrite IHcount | ]; reflexivity. }
  Qed.
  Lemma pre_redc_cps_id {cpsT} f : @pre_redc_cps cpsT f = f pre_redc.
  Proof.
    unfold pre_redc, pre_redc_cps.
    etransitivity; rewrite redc_loop_cps_id; [ | reflexivity ]; break_innermost_match;
      reflexivity.
  Qed.
  Lemma redc_cps_id {cpsT} f : @redc_cps cpsT f = f redc.
  Proof.
    unfold redc, redc_cps.
    etransitivity; rewrite pre_redc_cps_id; [ | reflexivity ];
      autorewrite with uncps;
      reflexivity.
  Qed.

  Lemma redc_body_id_no_cps pred_A_numlimbs A' S'
    : @redc_body pred_A_numlimbs A' B k S' = redc_body_no_cps B k (A', S').
  Proof.
    unfold redc_body, redc_body_cps, redc_body_no_cps, Abstract.Dependent.Definition.redc_body, LetIn.Let_In, id.
    repeat autounfold with word_by_word_montgomery.
    repeat first [ reflexivity
                 | progress cbn [fst snd id]
                 | progress autorewrite with uncps
                 | break_innermost_match_step
                 | f_equal; [] ].
  Qed.
  Lemma redc_loop_cps_id_no_cps count A_S
    : redc_loop count A_S = redc_loop_no_cps count A_S.
  Proof.
    unfold redc_loop_no_cps, id.
    revert A_S.
    induction count as [|count IHcount]; simpl; [ reflexivity | ].
    intros [A' S']; unfold redc_loop; simpl.
    rewrite redc_body_cps_id, redc_loop_cps_id, IHcount, redc_body_id_no_cps.
    reflexivity.
  Qed.
  Lemma pre_redc_cps_id_no_cps : pre_redc = pre_redc_no_cps.
  Proof.
    unfold pre_redc, pre_redc_cps, pre_redc_no_cps, Abstract.Dependent.Definition.pre_redc.
    rewrite redc_loop_cps_id, (surjective_pairing (redc_loop _ _)).
    rewrite redc_loop_cps_id_no_cps; reflexivity.
  Qed.
  Lemma redc_cps_id_no_cps : redc = redc_no_cps.
  Proof.
    unfold redc, redc_no_cps, redc_cps, Abstract.Dependent.Definition.redc.
    rewrite pre_redc_cps_id, pre_redc_cps_id_no_cps.
    autorewrite with uncps; reflexivity.
  Qed.

  Lemma redc_bound : 0 <= eval redc < R.
  Proof. rewrite redc_cps_id_no_cps; apply redc_no_cps_bound. Qed.
  Lemma redc_bound_N : eval B < eval N -> 0 <= eval redc < eval N.
  Proof. rewrite redc_cps_id_no_cps; apply redc_no_cps_bound_N. Qed.
  Lemma redc_mod_N
    : (eval redc) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
  Proof. rewrite redc_cps_id_no_cps; apply redc_no_cps_mod_N. Qed.
  Lemma small_redc
    : small redc.
  Proof. rewrite redc_cps_id_no_cps; apply small_redc_no_cps. Qed.

  Section add_sub.
    Context (Av Bv : T R_numlimbs)
            (small_Av : small Av)
            (small_Bv : small Bv)
            (Av_bound : 0 <= eval Av < eval N)
            (Bv_bound : 0 <= eval Bv < eval N).
    Local Notation add_no_cps := (@add_no_cps r R_numlimbs N Av Bv).
    Local Notation add_cps := (@add_cps r R_numlimbs N Av Bv).
    Local Notation add := (@add r R_numlimbs N Av Bv).
    Local Notation sub_no_cps := (@sub_no_cps r R_numlimbs N Av Bv).
    Local Notation sub_cps := (@sub_cps r R_numlimbs N Av Bv).
    Local Notation sub := (@sub r R_numlimbs N Av Bv).
    Local Notation opp_no_cps := (@opp_no_cps r R_numlimbs N Av).
    Local Notation opp_cps := (@opp_cps r R_numlimbs N Av).
    Local Notation opp := (@opp r R_numlimbs N Av).
    Local Notation sub_then_maybe_add_cps :=
       (fun p q => @sub_then_maybe_add_cps (Z.pos r) R_numlimbs (Z.pos r - 1) p q N).
    Local Notation sub_then_maybe_add :=
      (fun p q => @sub_then_maybe_add (Z.pos r) R_numlimbs (Z.pos r - 1) p q N).
    Local Notation eval_sub_then_maybe_add :=
      (fun p q smp smq => @eval_sub_then_maybe_add (Z.pos r) (Zorder.Zgt_pos_0 _) _ (Z.pos r - 1) p q N smp smq small_N N_mask).
    Local Notation small_sub_then_maybe_add :=
      (fun p q => @small_sub_then_maybe_add (Z.pos r) (Zorder.Zgt_pos_0 _) _ (Z.pos r - 1) p q N).

    Definition add_no_cps_bound : 0 <= eval add_no_cps < eval N
      := @add_bound T (@eval) r R R_numlimbs (@small) (@addT) (@eval_addT) (@small_addT) N N_lt_R (@conditional_sub) (@eval_conditional_sub) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition sub_no_cps_bound : 0 <= eval sub_no_cps < eval N
      := @sub_bound T (@eval) r R R_numlimbs (@small) N (@sub_then_maybe_add) (@eval_sub_then_maybe_add) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition opp_no_cps_bound : 0 <= eval opp_no_cps < eval N
      := @opp_bound T (@eval) (@zero) r R R_numlimbs (@small) (@eval_zero) (@small_zero) N (@sub_then_maybe_add) (@eval_sub_then_maybe_add) Av small_Av Av_bound.

    Definition small_add_no_cps : small add_no_cps
      := @small_add T (@eval) r R R_numlimbs (@small) (@addT) (@eval_addT) (@small_addT) N N_lt_R (@conditional_sub) (@small_conditional_sub) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition small_sub_no_cps : small sub_no_cps
      := @small_sub T R_numlimbs (@small) (@sub_then_maybe_add) (@small_sub_then_maybe_add) Av Bv.
    Definition small_opp_no_cps : small opp_no_cps
      := @small_opp T (@zero) R_numlimbs (@small) (@sub_then_maybe_add) (@small_sub_then_maybe_add) Av.

    Definition eval_add_no_cps : eval add_no_cps = eval Av + eval Bv + (if eval N <=? eval Av + eval Bv then - eval N else 0)
      := @eval_add T (@eval) r R R_numlimbs (@small) (@addT) (@eval_addT) (@small_addT) N N_lt_R (@conditional_sub) (@eval_conditional_sub) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition eval_sub_no_cps : eval sub_no_cps = eval Av - eval Bv + (if eval Av - eval Bv <? 0 then eval N else 0)
      := @eval_sub T (@eval) R_numlimbs (@small) N (@sub_then_maybe_add) (@eval_sub_then_maybe_add) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition eval_opp_no_cps : eval opp_no_cps = (if eval Av =? 0 then 0 else eval N) - eval Av
      := @eval_opp T (@eval) (@zero) r R R_numlimbs (@small) (@eval_zero) (@small_zero) N (@sub_then_maybe_add ) (@eval_sub_then_maybe_add) Av small_Av Av_bound.

    Definition eval_add_no_cps_mod_N : eval add_no_cps mod eval N = (eval Av + eval Bv) mod eval N
      := @eval_add_mod_N T (@eval) r R R_numlimbs (@small) (@addT) (@eval_addT) (@small_addT) N N_lt_R (@conditional_sub) (@eval_conditional_sub) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition eval_sub_no_cps_mod_N : eval sub_no_cps mod eval N = (eval Av - eval Bv) mod eval N
      := @eval_sub_mod_N T (@eval) R_numlimbs (@small) N (@sub_then_maybe_add) (@eval_sub_then_maybe_add) Av Bv small_Av small_Bv Av_bound Bv_bound.
    Definition eval_opp_no_cps_mod_N : eval opp_no_cps mod eval N = (-eval Av) mod eval N
      := @eval_opp_mod_N T (@eval) (@zero) r R R_numlimbs (@small) (@eval_zero) (@small_zero) N (@sub_then_maybe_add) (@eval_sub_then_maybe_add) Av small_Av Av_bound.

    Lemma add_cps_id_no_cps : add = add_no_cps.
    Proof.
      unfold add_no_cps, add, add_cps, Abstract.Dependent.Definition.add; autorewrite with uncps; reflexivity.
    Qed.
    Lemma sub_cps_id_no_cps : sub = sub_no_cps.
    Proof.
      unfold sub_no_cps, sub, sub_cps, Abstract.Dependent.Definition.sub; autorewrite with uncps; reflexivity.
    Qed.
    Lemma opp_cps_id_no_cps : opp = opp_no_cps.
    Proof.
      unfold opp, opp_cps, opp_no_cps, Abstract.Dependent.Definition.opp, sub_no_cps, sub, sub_cps, Abstract.Dependent.Definition.sub; autorewrite with uncps; reflexivity.
    Qed.

    Lemma add_cps_id {cpsT} f : @add_cps cpsT f = f add.
    Proof. unfold add, add_cps; autorewrite with uncps; reflexivity. Qed.
    Lemma sub_cps_id {cpsT} f : @sub_cps cpsT f = f sub.
    Proof. unfold sub, sub_cps; autorewrite with uncps. reflexivity. Qed.
    Lemma opp_cps_id {cpsT} f : @opp_cps cpsT f = f opp.
    Proof. unfold opp, opp_cps, sub, sub_cps; autorewrite with uncps. reflexivity. Qed.

    Local Ltac do_rewrite :=
      first [ rewrite add_cps_id_no_cps
            | rewrite sub_cps_id_no_cps
            | rewrite opp_cps_id_no_cps ].
    Local Ltac do_apply :=
      first [ apply add_no_cps_bound
            | apply sub_no_cps_bound
            | apply opp_no_cps_bound
            | apply small_add_no_cps
            | apply small_sub_no_cps
            | apply small_opp_no_cps
            | apply eval_add_no_cps
            | apply eval_sub_no_cps
            | apply eval_opp_no_cps
            | apply eval_add_no_cps_mod_N
            | apply eval_sub_no_cps_mod_N
            | apply eval_opp_no_cps_mod_N ].
    Local Ltac t := do_rewrite; do_apply.

    Lemma add_bound : 0 <= eval add < eval N. Proof. t. Qed.
    Lemma sub_bound : 0 <= eval sub < eval N. Proof. t. Qed.
    Lemma opp_bound : 0 <= eval opp < eval N. Proof. t. Qed.

    Lemma small_add : small add. Proof. t. Qed.
    Lemma small_sub : small sub. Proof. t. Qed.
    Lemma small_opp : small opp. Proof. t. Qed.

    Lemma eval_add : eval add = eval Av + eval Bv + (if eval N <=? eval Av + eval Bv then - eval N else 0).
    Proof. t. Qed.
    Lemma eval_sub : eval sub = eval Av - eval Bv + (if eval Av - eval Bv <? 0 then eval N else 0).
    Proof. t. Qed.
    Lemma eval_opp : eval opp = (if eval Av =? 0 then 0 else eval N) - eval Av.
    Proof. t. Qed.

    Lemma eval_add_mod_N : eval add mod eval N = (eval Av + eval Bv) mod eval N.
    Proof. t. Qed.
    Lemma eval_sub_mod_N : eval sub mod eval N = (eval Av - eval Bv) mod eval N.
    Proof. t. Qed.
    Lemma eval_opp_mod_N : eval opp mod eval N = (-eval Av) mod eval N.
    Proof. t. Qed.
  End add_sub.

  Section nonzero.
    Lemma nonzero_cps_id Av {cpsT} f : @nonzero_cps R_numlimbs Av cpsT f = f (@nonzero R_numlimbs Av).
    Proof. unfold nonzero, nonzero_cps; autorewrite with uncps; reflexivity. Qed.

    Lemma eval_nonzero Av : small Av -> @nonzero R_numlimbs Av = 0 <-> eval Av = 0.
    Proof. apply eval_nonzero; lia. Qed.
  End nonzero.
End WordByWordMontgomery.

Hint Rewrite redc_body_cps_id redc_loop_cps_id pre_redc_cps_id redc_cps_id add_cps_id sub_cps_id opp_cps_id : uncps.
