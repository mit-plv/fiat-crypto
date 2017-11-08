Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.Tactics.VM.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Crypto.Specific.Framework.ArithmeticSynthesis.SquareFromMul.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

(** XXX TODO(jadep) FIXME: Should we sanity-check that we have 2^2k - 2^k - 1 / the right form of prime? *)
Ltac internal_pose_sqrt_s s sqrt_s :=
  let v := (eval vm_compute in (Z.log2 s / 2)) in
  cache_term (2^v) sqrt_s.

Section gen.
  Context (m : positive)
          (base : Q)
          (sz : nat)
          (s : Z)
          (c : list limb)
          (half_sz : nat)
          (sqrt_s : Z)
          (base_pos : (1 <= base)%Q)
          (sz_nonzero : sz <> 0%nat)
          (half_sz_nonzero : half_sz <> 0%nat)
          (s_nonzero : s <> 0%Z)
          (m_correct : Z.pos m = s - Associational.eval c)
          (sqrt_s_nonzero : sqrt_s <> 0)
          (sqrt_s_mod_m : sqrt_s ^ 2 mod Z.pos m = (sqrt_s + 1) mod Z.pos m).

  Local Notation wt := (wt_gen base).
  Local Notation wt_divides' := (wt_gen_divides' base base_pos).
  Local Notation wt_nonzero := (wt_gen_nonzero base base_pos).

  Definition goldilocks_mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          mul a b = goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id) }.
  Proof.
    eexists; cbv beta zeta; intros.
    cbv [goldilocks_mul_cps].
    autorewrite with pattern_runtime.
    reflexivity.
  Defined.

  Definition mul_sig'
    : { mul : (Z^sz -> Z^sz -> Z^sz)%type
      | forall a b : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          Positional.Fdecode (m := m) wt (mul a b) = (eval a * eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    pose proof (wt_gen0_1 base).
    let x := constr:(
               goldilocks_mul_cps (n:=half_sz) (n2:=sz) wt sqrt_s a b (fun ab => Positional.reduce_cps (n:=sz) wt s c ab id)) in
    presolve_op_F constr:(wt) x;
      [ cbv [goldilocks_mul_cps];
        autorewrite with pattern_runtime;
        reflexivity
      | ].
    reflexivity.
  Defined.
End gen.

Ltac pose_half_sz_nonzero half_sz half_sz_nonzero :=
  cache_proof_with_type_by
    (half_sz <> 0%nat)
    ltac:(cbv; congruence)
           half_sz_nonzero.

Ltac pose_mul_sig wt m base sz s c half_sz mul_sig :=
  let sqrt_s := fresh "sqrt_s" in
  let sqrt_s := internal_pose_sqrt_s s sqrt_s in
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [mul_sig'])
           { mul : (Z^sz -> Z^sz -> Z^sz)%type
           | forall a b : Z^sz,
               let eval := Positional.Fdecode (m := m) wt in
               Positional.Fdecode (m := m) wt (mul a b) = (eval a * eval b)%F }
           (mul_sig' m base sz s c half_sz sqrt_s)
           mul_sig.

Ltac pose_square_sig sz m wt mul_sig square_sig :=
  SquareFromMul.pose_square_sig sz m wt mul_sig square_sig.
