Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.FreezeUnfolder.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.CacheTerm.

Module Export Exports.
  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.
End Exports.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Ltac freeze_preunfold :=
  cbv [freeze freeze_cps Wrappers.Columns.unbalanced_sub_cps Wrappers.Columns.conditional_add_cps Core.Columns.from_associational_cps Core.Columns.nils Core.Columns.cons_to_nth_cps Core.Columns.compact_cps Wrappers.Columns.add_cps Core.Columns.compact_step_cps Core.Columns.compact_digit_cps].

Section gen.
  Context (m : positive)
          (sz : nat)
          (c : list limb)
          (bitwidth : Z)
          (m_enc : Z^sz)
          (sz_nonzero : sz <> 0%nat)
          (sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m)).

  Local Notation wt := (wt_gen m sz).
  Local Notation sz2 := (sz2' sz).
  Local Notation wt_divides' := (wt_gen_divides' m sz sz_nonzero sz_le_log2_m).
  Local Notation wt_nonzero := (wt_gen_nonzero m sz).

  Context (c_small : 0 < Associational.eval c < wt sz)
          (m_enc_bounded : Tuple.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_enc_correct : Positional.eval wt m_enc = Z.pos m)
          (m_correct_wt : Z.pos m = wt sz - Associational.eval c).

  Definition freeze_sig'
    : { freeze : (Z^sz -> Z^sz)%type |
        forall a : Z^sz,
          (0 <= Positional.eval wt a < 2 * Z.pos m)->
          let eval := Positional.Fdecode (m := m) wt in
          eval (freeze a) = eval a }.
  Proof.
    eexists; cbv beta zeta; (intros a ?).
    pose proof wt_nonzero; pose proof (wt_gen_pos m sz).
    pose proof (wt_gen0_1 m sz).
    pose proof div_mod; pose proof (wt_gen_divides m sz sz_nonzero sz_le_log2_m).
    pose proof (wt_gen_multiples m sz).
    pose proof div_correct; pose proof modulo_correct.
    pose proof (wt_gen_divides_chain m sz sz_nonzero sz_le_log2_m).
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    presolve_op_F constr:(wt) x;
      [ autorewrite with pattern_runtime; reflexivity | ].
    rewrite eval_freeze with (c := c);
      try eassumption; try omega; try reflexivity.
  Defined.
End gen.

Ltac pose_freeze_sig wt m sz c bitwidth m_enc sz_nonzero sz_le_log2_m freeze_sig :=
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [freeze_sig'])
           {freeze : (Z^sz -> Z^sz)%type |
            forall a : Z^sz,
              (0 <= Positional.eval wt a < 2 * Z.pos m)->
              let eval := Positional.Fdecode (m := m) wt in
              eval (freeze a) = eval a}
           (freeze_sig' m sz c bitwidth m_enc sz_nonzero sz_le_log2_m)
           freeze_sig.
