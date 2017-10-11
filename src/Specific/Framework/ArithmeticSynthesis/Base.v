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
Ltac pose_wt_nonzero wt wt_nonzero :=
  cache_proof_with_type_by
    (forall i, wt i <> 0)
    ltac:(eapply pow_ceil_mul_nat_nonzero; vm_decide_no_check)
           wt_nonzero.
Ltac pose_wt_nonneg wt wt_nonneg :=
  cache_proof_with_type_by
    (forall i, 0 <= wt i)
    ltac:(apply pow_ceil_mul_nat_nonneg; vm_decide_no_check)
           wt_nonneg.
Ltac pose_wt_divides wt wt_divides :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i > 0)
    ltac:(apply pow_ceil_mul_nat_divide; vm_decide_no_check)
           wt_divides.
Ltac pose_wt_divides' wt wt_divides wt_divides' :=
  cache_proof_with_type_by
    (forall i, wt (S i) / wt i <> 0)
    ltac:(symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides)
           wt_divides'.
Ltac helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chain :=
  cache_term_with_type_by
    (forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
    ltac:(let i := fresh "i" in intros i ?; exact (wt_divides' i))
           wt_divides_chain.
Ltac internal_pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains :=
  lazymatch carry_chains with
  | ?carry_chain :: nil
    => helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chains
  | ?carry_chain :: ?carry_chains
    => let wt_divides_chains := fresh wt_divides_chains in
       let wt_divides_chain := fresh wt_divides_chains in
       let wt_divides_chain := helper_pose_wt_divides_chain wt carry_chain wt_divides' wt_divides_chain in
       let wt_divides_chains := internal_pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains in
       constr:((wt_divides_chain, wt_divides_chains))
  end.
Ltac pose_wt_divides_chains wt carry_chains wt_divides' wt_divides_chains :=
  let carry_chains := (eval cbv delta [carry_chains] in carry_chains) in
  internal_pose_wt_divides_chains' wt carry_chains wt_divides' wt_divides_chains.

Ltac pose_wt_pos wt wt_pos :=
  cache_proof_with_type_by
    (forall i, wt i > 0)
    ltac:(eapply pow_ceil_mul_nat_pos; vm_decide_no_check)
           wt_pos.

Ltac pose_wt_multiples wt wt_multiples :=
  cache_proof_with_type_by
    (forall i, wt (S i) mod (wt i) = 0)
    ltac:(apply pow_ceil_mul_nat_multiples; vm_decide_no_check)
           wt_multiples.
