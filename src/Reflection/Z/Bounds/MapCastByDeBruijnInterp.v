Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Z.MapCastByDeBruijnInterp.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.Bounds.InterpretationLemmas.
Require Import Crypto.Reflection.Z.Bounds.MapCastByDeBruijn.

Lemma MapCastCorrect
      {t} (e : Expr base_type op t)
      (Hwf : Wf e)
      (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
  : forall {b} e' (He':MapCast e input_bounds = Some (existT _ b e'))
           v v' (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v),
    Interp (@Bounds.interp_op) e input_bounds = b
    /\ Bounds.is_bounded_by b (Interp interp_op e v)
    /\ cast_back_flat_const (Interp interp_op e' v') = (Interp interp_op e v).
Proof.
  apply MapCastCorrect; auto.
  { apply is_bounded_by_interp_op. }
  { apply pull_cast_genericize_op. }
Qed.
