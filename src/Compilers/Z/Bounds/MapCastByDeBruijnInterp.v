Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Z.MapCastByDeBruijnInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijn.

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
