Require Import Coq.ZArith.ZArith.
Require Import Coq.romega.ROmega.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Decidable.

Require Crypto.Arithmetic.Saturated.MontgomeryAPI.

Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.

Ltac pose_meval feBW_tight r meval :=
  cache_term_with_type_by
    (feBW_tight -> Z)
    ltac:(exact (fun x : feBW_tight => MontgomeryAPI.eval (Z.pos r) (BoundedWordToZ _ _ _ x)))
           meval.

Ltac pose_feBW_small sz feBW_tight meval r m_enc feBW_small :=
  cache_term
    { v : feBW_tight | meval v < MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc }
    feBW_small.

Ltac pose_feBW_tight_of_feBW_small feBW_tight feBW_small feBW_tight_of_feBW_small :=
  cache_term_with_type_by
    (feBW_small -> feBW_tight)
    ltac:(refine (@proj1_sig _ _))
           feBW_tight_of_feBW_small.

Ltac pose_phiM feBW_tight m meval montgomery_to_F phiM :=
  cache_term_with_type_by
    (feBW_tight -> F m)
    ltac:(exact (fun x : feBW_tight => montgomery_to_F (meval x)))
           phiM.

Ltac pose_phiM_small feBW_small feBW_tight_of_feBW_small m meval montgomery_to_F phiM_small :=
  cache_term_with_type_by
    (feBW_small -> F m)
    ltac:(exact (fun x : feBW_small => montgomery_to_F (meval (feBW_tight_of_feBW_small x))))
           phiM_small.
