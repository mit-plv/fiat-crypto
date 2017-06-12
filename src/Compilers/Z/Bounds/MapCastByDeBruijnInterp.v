Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Z.MapCastByDeBruijnInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.InterpSideConditions.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.IsBoundedBy.
Require Import Crypto.Compilers.Z.Bounds.InterpretationLemmas.PullCast.
Require Import Crypto.Compilers.Z.Bounds.MapCastByDeBruijn.
Require Import Crypto.Util.PointedProp.

Lemma MapCastCorrect
      {round_up}
      {t} (e : Expr base_type op t)
      (Hwf : Wf e)
      (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
  : forall {b} e' (He':MapCast round_up e input_bounds = Some (existT _ b e'))
           v v' (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
           (Hside : to_prop (InterpSideConditions e v)),
    Interp (@Bounds.interp_op) e input_bounds = b
    /\ Bounds.is_bounded_by b (Interp interp_op e v)
    /\ cast_back_flat_const (Interp interp_op e' v') = (Interp interp_op e v).
Proof.
  apply MapCastCorrect; auto.
  { apply is_bounded_by_interp_op. }
  { apply pull_cast_genericize_op, is_bounded_by_interp_op. }
Qed.

Lemma MapCastCorrect_eq
      {round_up}
      {t} (e : Expr base_type op t)
      {evb ev}
      (Hwf : Wf e)
      (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
  : forall {b} e' (He':MapCast round_up e input_bounds = Some (existT _ b e'))
           v v' (Hv : Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
           (Hside : to_prop (InterpSideConditions e v))
           (Hevb : evb = Interp (@Bounds.interp_op) e input_bounds)
           (Hev : ev = Interp interp_op e v),
    evb = b
    /\ Bounds.is_bounded_by b ev
    /\ cast_back_flat_const (Interp interp_op e' v') = ev.
Proof.
  intros; subst; apply MapCastCorrect; auto.
Qed.
