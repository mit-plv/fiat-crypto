Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.ArithmeticCPS.BaseConversion.
Require Import Crypto.ArithmeticCPS.Core.
Require Import Crypto.ArithmeticCPS.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.ArithmeticCPS.Saturated.
Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Opp.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Import CPSBindNotations.
Local Open Scope cps_scope.

(* TODO: rename this module? (Should it be, e.g., [Rows.freeze]?) *)
Module Freeze (Import RT : Runtime).
  Module Import Deps.
    Module Rows := Rows RT.
  End Deps.
  Section Freeze.
    Context (weight : nat -> Z).

    Definition freeze_cps n mask (m p:list Z) : ~> list Z :=
      (p_carry <- Rows.sub_cps weight n p m;
         let '(p, carry) := p_carry in
         r_carry <- Rows.conditional_add_cps weight n mask (-carry)%RT p m;
           let '(r, carry) := r_carry in
           return r).
  End Freeze.
End Freeze.

Module FreezeModOps (Import RT : Runtime).
  Module Import Deps.
    Module Export Positional := Positional RT.
    Module Export Freeze := Freeze RT.
    Module BaseConversion := BaseConversion RT.
    Module Export Core.
      Module Associational := ArithmeticCPS.Core.Associational RT.
    End Core.
  End Deps.
  Section mod_ops.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (bitwidth : Z)
          (m_enc : list Z)
          (Hn_nz : n <> 0%nat).
  Local Notation bytes_weight := (@weight 8 1).
  Local Notation weight := (@weight limbwidth_num limbwidth_den).
  Let m := (s - Associational.eval c).

  Context (Hs : s = weight n).
  Context (c_small : 0 < Associational.eval c < weight n)
          (m_enc_bounded : List.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_enc_correct : Positional.eval weight n m_enc = m)
          (Hm_enc_len : length m_enc = n).

  Definition bytes_n
    := Eval cbv [Qceiling Qdiv inject_Z Qfloor Qmult Qopp Qnum Qden Qinv Pos.mul]
      in Z.to_nat (Qceiling (Z.log2_up (weight n) / 8)).

  Definition to_bytes_cps (v : list Z) : ~> _
    := BaseConversion.convert_bases_cps weight bytes_weight n bytes_n v.

  Definition from_bytes_cps (v : list Z) : ~> _
    := BaseConversion.convert_bases_cps bytes_weight weight bytes_n n v.

  Definition freeze_to_bytesmod_cps (f : list Z) : ~> list Z
    := (f <- freeze_cps weight n (Z.ones bitwidth) m_enc f; to_bytes_cps f).

  Definition to_bytesmod_cps (f : list Z) : ~> list Z
    := to_bytes_cps f.
  Definition to_bytesmod (f : list Z) : list Z := to_bytesmod_cps f _ id.

  Definition from_bytesmod_cps (f : list Z) : ~> list Z
    := from_bytes_cps f.
  Definition from_bytesmod (f : list Z) : list Z := from_bytesmod_cps f _ id.
  End mod_ops.
End FreezeModOps.
