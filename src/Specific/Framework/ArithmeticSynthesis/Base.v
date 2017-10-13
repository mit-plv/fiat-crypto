Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.Decidable.
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
  Definition wt_gen (m : positive) (sz : nat) (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
End wt.
Ltac pose_wt m sz wt :=
  let v := (eval cbv [wt_gen] in (wt_gen m sz)) in
  cache_term v wt.

Ltac pose_sz2 sz sz2 :=
  let v := (eval vm_compute in ((sz * 2) - 1)%nat) in
  cache_term v sz2.

Ltac pose_half_sz sz half_sz :=
  let v := (eval compute in (sz / 2)%nat) in
  cache_term v half_sz.

Ltac pose_half_sz_nonzero half_sz half_sz_nonzero :=
  cache_proof_with_type_by
    (half_sz <> 0%nat)
    ltac:(cbv; congruence)
           half_sz_nonzero.

Ltac pose_m_enc sz s c wt m_enc :=
  let v := (eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c))) in
  let v := (eval compute in v) in (* compute away the type arguments *)
  cache_term v m_enc.
Ltac pose_coef sz wt m_enc coef_div_modulus coef := (* subtraction coefficient *)
  let v := (eval vm_compute in
               ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
                   match ctr with
                   | O => acc
                   | S n => addm (Positional.add_cps wt acc m_enc id) n
                   end) (Positional.zeros sz) coef_div_modulus)) in
  cache_term v coef.

Ltac pose_coef_mod sz wt m coef coef_mod :=
  cache_term_with_type_by
    (mod_eq m (Positional.eval (n:=sz) wt coef) 0)
    ltac:(exact eq_refl)
           coef_mod.
Ltac pose_sz_nonzero sz sz_nonzero :=
  cache_proof_with_type_by
    (sz <> 0%nat)
    ltac:(vm_decide_no_check)
           sz_nonzero.
Section wt_gen.
  Context (m : positive) (sz : nat).
  Local Notation wt := (wt_gen m sz).
  Local Ltac Q_cbv :=
    cbv [wt_gen Qround.Qceiling QArith_base.Qmult QArith_base.Qdiv QArith_base.inject_Z QArith_base.Qden QArith_base.Qnum QArith_base.Qopp Qround.Qfloor QArith_base.Qinv QArith_base.Qle Z.of_nat].
  Lemma wt_gen0_1 : wt 0 = 1.
  Proof.
    Q_cbv; simpl.
    autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma wt_gen_nonzero : forall i, wt i <> 0.
  Proof.
    eapply pow_ceil_mul_nat_nonzero; [ omega | ].
    destruct sz; Q_cbv;
      autorewrite with zsimplify_const; [ omega | ].
    apply Z.log2_up_nonneg.
  Qed.

  Lemma wt_gen_nonneg : forall i, 0 <= wt i.
  Proof. apply pow_ceil_mul_nat_nonneg; omega. Qed.

  Lemma wt_gen_pos : forall i, wt i > 0.
  Proof.
    intro i; pose proof (wt_gen_nonzero i); pose proof (wt_gen_nonneg i).
    omega.
  Qed.

  Lemma wt_gen_multiples : forall i, wt (S i) mod (wt i) = 0.
  Proof.
    apply pow_ceil_mul_nat_multiples.
    destruct sz; Q_cbv; autorewrite with zsimplify_const;
      auto using Z.log2_up_nonneg, Z.le_refl.
  Qed.

  Section divides.
    Context (sz_nonzero : sz <> 0%nat)
            (sz_small : Z.of_nat sz <= Z.log2_up (Z.pos m)).

    Lemma wt_gen_divides
      : forall i, wt (S i) / wt i > 0.
    Proof.
      apply pow_ceil_mul_nat_divide; [ omega | ].
      destruct sz; Q_cbv; autorewrite with zsimplify_const; [ congruence | ].
      rewrite Pos.mul_1_l; assumption.
    Qed.
    Lemma wt_gen_divides'
      : forall i, wt (S i) / wt i <> 0.
    Proof.
      symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_gen_divides; assumption.
    Qed.

    Lemma wt_gen_div_bound
      : forall i, wt (S i) / wt i <= wt 1.
    Proof.
      intro; etransitivity.
      eapply pow_ceil_mul_nat_divide_upperbound; [ omega | ].
      all:destruct sz; Q_cbv; autorewrite with zsimplify_const;
        rewrite ?Pos.mul_1_l, ?Pos.mul_1_r; try assumption; omega.
    Qed.
    Lemma wt_gen_divides_chain
          carry_chain
      : forall i (H:In i carry_chain), wt (S i) / wt i <> 0.
    Proof. intros i ?; apply wt_gen_divides'; assumption. Qed.

    Lemma wt_gen_divides_chains
          carry_chains
      : List.fold_right
          and
          True
          (List.map
             (fun carry_chain
              => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
             carry_chains).
    Proof.
      induction carry_chains as [|carry_chain carry_chains IHcarry_chains];
        constructor; eauto using wt_gen_divides_chain.
    Qed.
  End divides.
End wt_gen.


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
    ltac:(refine (@wt_gen_divides_chains _ _ _ _ carry_chains); vm_decide_no_check)
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
