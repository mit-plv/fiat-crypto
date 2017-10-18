Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith_base.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.CacheTerm.

  (* emacs for adjusting definitions *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_ \.]*\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      (\2)^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.): *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\3^J  let v := P.do_compute \2 in cache_term v \1.):  *)

Ltac pose_r bitwidth r :=
  cache_term_with_type_by
    positive
    ltac:(let v := (eval vm_compute in (Z.to_pos (2^bitwidth))) in exact v)
           r.

Ltac pose_m s c m := (* modulus *)
  let v := (eval vm_compute in (Z.to_pos (s - Associational.eval c))) in
  cache_term v m.

Section wt.
  Import QArith Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion Z.pos : positive >-> Z.
  Definition wt_gen (base : Q) (i:nat) : Z := 2^Qceiling(base*i).
End wt.

Section gen.
  Context (base : Q)
          (m : positive)
          (sz : nat)
          (coef_div_modulus : nat)
          (base_pos : (1 <= base)%Q).

  Local Notation wt := (wt_gen base).

  Definition sz2' := ((sz * 2) - 1)%nat.

  Definition half_sz' := (sz / 2)%nat.

  Definition m_enc'
    := Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (Z.pos m).

  Lemma sz2'_nonzero
        (sz_nonzero : sz <> 0%nat)
    : sz2' <> 0%nat.
  Proof using Type. clear -sz_nonzero; cbv [sz2']; omega. Qed.

  Local Ltac Q_cbv :=
    cbv [wt_gen Qround.Qceiling QArith_base.Qmult QArith_base.Qdiv QArith_base.inject_Z QArith_base.Qden QArith_base.Qnum QArith_base.Qopp Qround.Qfloor QArith_base.Qinv QArith_base.Qle QArith_base.Qeq Z.of_nat] in *.
  Lemma wt_gen0_1 : wt 0 = 1.
  Proof using Type.
    Q_cbv; simpl.
    autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma wt_gen_nonzero : forall i, wt i <> 0.
  Proof using base_pos.
    eapply pow_ceil_mul_nat_nonzero; [ omega | ].
    destruct base; Q_cbv; lia.
  Qed.

  Lemma wt_gen_nonneg : forall i, 0 <= wt i.
  Proof using Type. apply pow_ceil_mul_nat_nonneg; omega. Qed.

  Lemma wt_gen_pos : forall i, wt i > 0.
  Proof using base_pos.
    intro i; pose proof (wt_gen_nonzero i); pose proof (wt_gen_nonneg i).
    omega.
  Qed.

  Lemma wt_gen_multiples : forall i, wt (S i) mod (wt i) = 0.
  Proof using base_pos.
    apply pow_ceil_mul_nat_multiples; destruct base; Q_cbv; lia.
  Qed.

  Section divides.
    Lemma wt_gen_divides
      : forall i, wt (S i) / wt i > 0.
    Proof using base_pos.
      apply pow_ceil_mul_nat_divide; [ omega | ].
      destruct base; Q_cbv; lia.
    Qed.

    Lemma wt_gen_divides'
      : forall i, wt (S i) / wt i <> 0.
    Proof using base_pos.
      symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_gen_divides; assumption.
    Qed.

    Lemma wt_gen_div_bound
      : forall i, wt (S i) / wt i <= wt 1.
    Proof using base_pos.
      intro; etransitivity.
      eapply pow_ceil_mul_nat_divide_upperbound; [ omega | ].
      all:destruct base; Q_cbv; autorewrite with zsimplify_const;
        rewrite ?Pos.mul_1_l, ?Pos.mul_1_r; try assumption; omega.
    Qed.
    Lemma wt_gen_divides_chain
          carry_chain
      : forall i (H:In i carry_chain), wt (S i) / wt i <> 0.
    Proof using base_pos. intros i ?; apply wt_gen_divides'; assumption. Qed.

    Lemma wt_gen_divides_chains
          carry_chains
      : List.fold_right
          and
          True
          (List.map
             (fun carry_chain
              => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
             carry_chains).
    Proof using base_pos.
      induction carry_chains as [|carry_chain carry_chains IHcarry_chains];
        constructor; eauto using wt_gen_divides_chain.
    Qed.
  End divides.

  Definition coef'
    := (fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
          match ctr with
          | O => acc
          | S n => addm (Positional.add_cps wt acc m_enc' id) n
          end) (Positional.zeros sz) coef_div_modulus.

  Lemma coef_mod'
    : mod_eq m (Positional.eval (n:=sz) wt coef') 0.
  Proof using base_pos.
    cbv [coef' m_enc'].
    remember (Positional.zeros sz) as v eqn:Hv.
    assert (Hv' : mod_eq m (Positional.eval wt v) 0)
      by (subst v; autorewrite with push_basesystem_eval; reflexivity);
      clear Hv.
    revert dependent v.
    induction coef_div_modulus as [|n IHn]; clear coef_div_modulus;
      intros; [ assumption | ].
    rewrite IHn; [ reflexivity | ].
    pose proof wt_gen0_1.
    pose proof wt_gen_nonzero.
    pose proof div_mod.
    pose proof wt_gen_divides'.
    destruct (Nat.eq_dec sz 0).
    { subst; reflexivity. }
    { repeat autounfold; autorewrite with uncps push_id push_basesystem_eval.
      rewrite Positional.eval_encode by auto.
      cbv [mod_eq] in *.
      push_Zmod; rewrite Hv'; pull_Zmod.
      reflexivity. }
  Qed.
End gen.

Ltac pose_wt base wt :=
  let v := (eval cbv [wt_gen] in (wt_gen base)) in
  cache_term v wt.

Ltac pose_sz2 sz sz2 :=
  let v := (eval vm_compute in (sz2' sz)) in
  cache_term v sz2.

Ltac pose_half_sz sz half_sz :=
  let v := (eval compute in (half_sz' sz)) in
  cache_term v half_sz.

Ltac pose_half_sz_nonzero half_sz half_sz_nonzero :=
  cache_proof_with_type_by
    (half_sz <> 0%nat)
    ltac:(cbv; congruence)
           half_sz_nonzero.

Ltac pose_s_nonzero s s_nonzero :=
  cache_proof_with_type_by
    (s <> 0)
    ltac:(vm_decide_no_check)
           s_nonzero.

Ltac pose_sz_le_log2_m sz m sz_le_log2_m :=
  cache_proof_with_type_by
    (Z.of_nat sz <= Z.log2_up (Z.pos m))
    ltac:(vm_decide_no_check)
           sz_le_log2_m.

Ltac pose_base_pos base base_pos :=
  cache_proof_with_type_by
    ((1 <= base)%Q)
    ltac:(vm_decide_no_check)
           base_pos.

Ltac pose_m_correct m s c m_correct :=
  cache_proof_with_type_by
    (Z.pos m = s - Associational.eval c)
    ltac:(vm_decide_no_check)
           m_correct.

Ltac pose_m_enc base m sz m_enc :=
  let v := (eval vm_compute in (m_enc' base m sz)) in
  let v := (eval compute in v) in (* compute away the type arguments *)
  cache_term v m_enc.

Ltac pose_coef base m sz coef_div_modulus coef := (* subtraction coefficient *)
  let v := (eval vm_compute in (coef' base m sz coef_div_modulus)) in
  cache_term v coef.

Ltac pose_coef_mod wt coef base m sz coef_div_modulus base_pos coef_mod :=
  cache_proof_with_type_by
    (mod_eq m (Positional.eval (n:=sz) wt coef) 0)
    ltac:(vm_cast_no_check (coef_mod' base m sz coef_div_modulus base_pos))
           coef_mod.
Ltac pose_sz_nonzero sz sz_nonzero :=
  cache_proof_with_type_by
    (sz <> 0%nat)
    ltac:(vm_decide_no_check)
           sz_nonzero.

Ltac pose_wt_nonzero wt wt_nonzero :=
  cache_proof_with_type_by
    (forall i, wt i <> 0)
    ltac:(apply wt_gen_nonzero; vm_decide_no_check)
           wt_nonzero.
Ltac pose_wt_nonneg wt wt_nonneg :=
  cache_proof_with_type_by
    (forall i, 0 <= wt i)
    ltac:(apply wt_gen_nonneg; vm_decide_no_check)
           wt_nonneg.
Ltac pose_wt_divides wt wt_divides :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i > 0)
    ltac:(apply wt_gen_divides; vm_decide_no_check)
           wt_divides.
Ltac pose_wt_divides' wt wt_divides wt_divides' :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i <> 0)
    ltac:(apply wt_gen_divides'; vm_decide_no_check)
           wt_divides'.

Ltac pose_wt_divides_chains wt carry_chains wt_divides_chains :=
  let T := (eval cbv [carry_chains List.fold_right List.map] in
               (List.fold_right
                  and
                  True
                  (List.map
                     (fun carry_chain
                      => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
                     carry_chains))) in
  cache_proof_with_type_by
    T
    ltac:(refine (@wt_gen_divides_chains _ _ carry_chains); vm_decide_no_check)
           wt_divides_chains.

Ltac pose_wt_pos wt wt_pos :=
  cache_proof_with_type_by
    (forall i, wt i > 0)
    ltac:(apply wt_gen_pos; vm_decide_no_check)
           wt_pos.

Ltac pose_wt_multiples wt wt_multiples :=
  cache_proof_with_type_by
    (forall i, wt (S i) mod (wt i) = 0)
    ltac:(apply wt_gen_multiples; vm_decide_no_check)
           wt_multiples.

Ltac pose_c_small c wt sz c_small :=
  cache_proof_with_type_by
    (0 < Associational.eval c < wt sz)
    ltac:(vm_decide_no_check)
           c_small.

Ltac pose_m_enc_bounded sz bitwidth m_enc m_enc_bounded :=
  cache_proof_with_type_by
    (Tuple.map (n:=sz) (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
    ltac:(vm_compute; reflexivity)
           m_enc_bounded.
